
(* ===================================================== *)
(* ============== CS4212 Compiler Design ============== *)
(*   Transformation to intermediary representation IR3   *)
(* ===================================================== *)

open MOOL_structs
open Ir3mOOL_structs

let labelcount = ref 0 
let fresh_label () = 
	(labelcount:=!labelcount+1; !labelcount)

let varcount = ref 0 
let fresh_var () = 
	(varcount:=!varcount+1; (string_of_int !varcount))

let create_temp_var () =
  ("_t" ^ (fresh_var ()))

(* Compare two variable ids *)  
let compare_var_ids v1 v2 =
  match v1,v2 with
  | SimpleVarId id1, SimpleVarId id2 -> 
     ((String.compare id1 id2) == 0)
  | SimpleVarId id1, TypedVarId (id2,t,s) -> 
     ((String.compare id1 id2) == 0)  
  | TypedVarId (id1,t,s), SimpleVarId id2 -> 
     ((String.compare id1 id2) == 0)    
  | TypedVarId (id1,t1,s1), TypedVarId (id2,t2 ,s2) ->
     ((String.compare id1 id2) == 0) && (s1 == s2)

(* Compare two types *)   
let compare_mOOL_types 
      (t1:mOOL_type) (t2:mOOL_type) = 
  match t1,t2 with 
  | (ObjectT name1), (ObjectT "null") -> true
  | (ObjectT name1), (ObjectT name2) -> 
     ((String.compare name1 name2) == 0) 
  | t1, t2 -> t1 == t2

(* Compare two types. It returns true if type2 is equals to type1 or type2 is child of type1 *)
let rec compare_mOOL_types_with_inheritance inheritance_table t1 t2 =
  match (t1, t2) with
  | (ObjectT name1), (ObjectT "null") -> true
  | (ObjectT name1), (ObjectT name2) ->
    if ((String.compare name1 name2) == 0)
      then true
    else begin
      let t2_parent = Hashtbl.find inheritance_table (Some name2) in
      match t2_parent with
      | Some t2_parent_name -> compare_mOOL_types_with_inheritance inheritance_table t1 (ObjectT t2_parent_name)
      | None -> false
    end
  | _, _ -> compare_mOOL_types t1 t2
  
(* Transform a MOOL program to IR3 *)
let mOOL_program_to_IR3 (p:mOOL_program):ir3_program=
  let (mainclass, classes) = p in

  let convert_ir3_type_to_string t =
    match t with
    | BoolT -> "Bool"
    | IntT -> "Int"
    | StringT -> "String"
    | VoidT -> "Void"
    | ObjectT c -> c
    | Unknown -> "" in

  let get_exp_type typed_exp =
    match typed_exp with
    | TypedExp (_, t) -> t
    | _ -> failwith "Error: method parameter expression does not have a valid type!" in

  let convert_var_id var_mOOL_id =
    match var_mOOL_id with
    | SimpleVarId v ->  v
    | TypedVarId (s, t, i)->  s in

  let convert_var_decl_list var_list =
    List.map(fun element -> 
      let (var_mOOL_type, var_mOOL_id) = element in
      let var_id3_id = convert_var_id var_mOOL_id in
      (var_mOOL_type, var_id3_id)
    ) var_list in

  let generate_signature m_name type_list =
    (String.concat "~" ((convert_var_id m_name) :: List.map(fun element -> (convert_ir3_type_to_string element)) type_list)) in

  (* Find the declared type of a variable *)    
  let rec find_var_decl_type var_list var_id =
    match var_list with
    | [] -> (Unknown, var_id)
    | (t,v)::tl ->
      if (compare_var_ids v var_id) 
        then (t,v)
      else (find_var_decl_type tl var_id) in

  let rec find_method_decl inheritance_table public_method_table current_class_methods class_name method_name param_type_list =
    let method_list = ref [] in
    method_list := current_class_methods @ !method_list;
    let rec build_method_list c =
      if (compare c None != 0)
        then begin
          method_list := !method_list @ (Hashtbl.find public_method_table c);
          build_method_list (Hashtbl.find inheritance_table c)
        end in
    build_method_list (Hashtbl.find inheritance_table class_name);
    let result_list = List.filter(fun m ->
      let m_param_type_list = List.map(fun element -> let x, _ = element in x) m.params in
      if (not (compare_var_ids m.mOOLid method_name) || (List.length param_type_list) != (List.length m_param_type_list))
        then false
      else begin
        let matched = ref true in
        List.iter2 (fun a b -> 
          if (not (compare_mOOL_types_with_inheritance inheritance_table a b))
            then matched := false;
        ) m_param_type_list param_type_list;
        !matched
      end
    ) !method_list in
    if (List.length result_list > 0)
      then List.hd result_list
    else
      failwith ("Error: illegal method call " ^ (string_of_var_id method_name) ^ "!") in

  let rec check_this exp = 
    match exp with
    | TypedExp (e, t) ->
      begin
        match e with
        | ThisWord -> "this"
        | TypedExp (e1, t1) -> check_this e1
        | _ -> "other"
      end
    | _ -> "other" in

  (* Create a temporary variable name for an expression *)
  let create_temp_id3_for_ir3_exp exp exp_type =
    match exp with
    | Idc3Expr (Var3 v) -> (v, [], [])
    | _ ->
      let temp_var_name = create_temp_var () in
      let temp_statement = AssignStmt3(temp_var_name, exp) in
      (temp_var_name, [(exp_type, temp_var_name)], [temp_statement]) in

  (* Create a temporary idc3 variable for an expression *)
  let create_temp_idc3_for_ir3_exp exp exp_type =
    match exp with
    | Idc3Expr e -> (e, [], [])
    | _ ->
      let temp_var_name = create_temp_var () in
      let temp_statement = AssignStmt3(temp_var_name, exp) in
      ((Var3 temp_var_name), [(exp_type, temp_var_name)], [temp_statement]) in

  (* Transform a method to IR3 *) 
  let mOOL_mddecl_to_IR3 cname m inheritance_table public_attribute_table public_method_table class_methods_table =
    let rec convert_statement_list statement_list =
      (* Returns expression type, ir3 Expression, temp var list, intermediate statement list *)
      let rec convert_expression typed_exp =
        match typed_exp with
        | TypedExp (exp, exp_type) ->
          begin
            match exp with
            | UnaryExp (op, e) ->
              let (e_type, ir3_e, temp_vars, temp_statements) = convert_expression e in
              let (id3_var, temp_id3_var, temp_statement) = create_temp_idc3_for_ir3_exp ir3_e e_type in
              (exp_type, UnaryExp3 (op, id3_var), temp_vars @ temp_id3_var, temp_statements @ temp_statement)
            | BinaryExp (op, e1, e2) ->
              let (e_type1, ir3_e1, temp_vars1, temp_statements1) = convert_expression e1 in
              let (e_type2, ir3_e2, temp_vars2, temp_statements2) = convert_expression e2 in
              (* Boolean short circuit *)
              begin
                match op with
                | BooleanOp "&&" ->
                  let true_label_num = fresh_label () in
                  let true_label_statement = Label3 true_label_num in
                  let next_label_num = fresh_label () in
                  let next_label_statement  = Label3 next_label_num in
                  let (id3_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp ir3_e1 e_type1 in
                  let short_circuit_statement = [IfStmt3 (ir3_e1, true_label_num)] @ temp_statement @ 
                    [GoTo3 next_label_num; true_label_statement; AssignStmt3 (id3_var_name, ir3_e2); next_label_statement] in

                  (exp_type, Idc3Expr (Var3 id3_var_name), temp_vars1 @ temp_vars2 @ temp_id3_var, 
                    temp_statements1 @ temp_statements2 @ short_circuit_statement)
                | BooleanOp "||" ->
                  let true_label_num = fresh_label () in
                  let true_label_statement = Label3 true_label_num in
                  let next_label_num = fresh_label () in
                  let next_label_statement  = Label3 next_label_num in
                  let (id3_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp ir3_e1 e_type1 in
                  let short_circuit_statement = [IfStmt3 (ir3_e1, true_label_num); AssignStmt3 (id3_var_name, ir3_e2); 
                    GoTo3 next_label_num; true_label_statement] @ temp_statement @ [next_label_statement] in

                  (exp_type, Idc3Expr (Var3 id3_var_name), temp_vars1 @ temp_vars2 @ temp_id3_var, 
                    temp_statements1 @ temp_statements2 @ short_circuit_statement)
                | _ -> (* Normal scenario *)
                  let (id3_var1, temp_id3_var1, temp_statement1) = create_temp_idc3_for_ir3_exp ir3_e1 e_type1 in
                  let (id3_var2, temp_id3_var2, temp_statement2) = create_temp_idc3_for_ir3_exp ir3_e2 e_type2 in
                  (exp_type, BinaryExp3 (op, id3_var1, id3_var2), temp_vars1 @ temp_vars2 @ temp_id3_var1 @ temp_id3_var2,
                    temp_statements1 @ temp_statements2 @ temp_statement1 @ temp_statement2)
              end
            | FieldAccess (e, id) ->
              let (e_type, ir3_e, temp_vars, temp_statements) = convert_expression e in
              let (id3_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp ir3_e e_type in
              (exp_type, FieldAccess3 (id3_var_name, convert_var_id id), temp_vars @ temp_id3_var, temp_statements @ temp_statement)
            | ObjectCreate c -> (exp_type, ObjectCreate3 c, [], [])
            | MdCall (e, param_exps) -> (* TODO: revise later *)
              let param_types = List.map get_exp_type param_exps in
              let temp_statements = ref [] in
              let temp_vars = ref [] in
              let param_idc3_list = ref [] in
              List.iter(fun param_exp -> 
                let (e_type, ir3_e, param_exp_temp_vars, param_exp_temp_statements) = convert_expression param_exp in
                let (id3_var, temp_id3_var, temp_statement) = create_temp_idc3_for_ir3_exp ir3_e e_type in
                temp_statements := !temp_statements @ param_exp_temp_statements @ temp_statement;
                temp_vars := !temp_vars @ param_exp_temp_vars @ temp_id3_var;
                param_idc3_list := !param_idc3_list @ [id3_var];
              ) param_exps;
              begin
                match e with
                | FieldAccess (o_exp, m_name) ->
                  let o_t = check_this o_exp in
                  let o_exp_type = get_exp_type o_exp in
                  let method_decl = 
                    if ((compare o_t "this" == 0) && compare_mOOL_types o_exp_type (ObjectT cname))
                      then begin
                        let class_option = (Some cname) in
                        let current_class_methods = Hashtbl.find class_methods_table class_option in
                        find_method_decl inheritance_table public_method_table current_class_methods class_option m_name param_types
                      end
                    else begin
                      let c = match o_exp_type with
                      | ObjectT c1 -> c1
                      | _ -> failwith "Error: wrong object!" in
                      let class_option = (Some c) in
                      let current_class_methods = Hashtbl.find public_method_table class_option in
                      find_method_decl inheritance_table public_method_table current_class_methods class_option m_name param_types
                    end
                  in
                  let new_m_name = generate_signature m_name (o_exp_type::(List.map(fun (x, _) -> x) method_decl.params)) in
                  let (o_exp_type, o_ir3_e, o_exp_temp_vars, o_exp_temp_statements) = convert_expression o_exp in
                  let (o_id3_var_name, o_temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp o_ir3_e o_exp_type in
                  (exp_type, MdCall3 (o_id3_var_name, new_m_name, !param_idc3_list), o_temp_id3_var @ !temp_vars, temp_statement @ !temp_statements)
                | Var (m_name) ->
                  let class_option = (Some cname) in
                  let current_class_methods = Hashtbl.find class_methods_table class_option in
                  let method_decl = find_method_decl inheritance_table public_method_table current_class_methods class_option m_name param_types in
                  let new_m_name = generate_signature m_name ((ObjectT cname)::(List.map(fun (x, _) -> x) method_decl.params)) in
                  (exp_type, MdCall3 ("this", new_m_name, !param_idc3_list), !temp_vars, !temp_statements)
                | _ -> failwith "Error: method expression cannot be recognized!"
              end
            | BoolLiteral b -> (exp_type, Idc3Expr (BoolLiteral3 b), [], [])
            | IntLiteral i -> (exp_type, Idc3Expr (IntLiteral3 i), [], [])
            | StringLiteral s -> (exp_type, Idc3Expr (StringLiteral3 s), [], [])
            | ThisWord -> (exp_type, Idc3Expr (Var3 "this"), [], [])
            | NullWord -> (exp_type, Idc3Expr (Var3 "null"), [], [])
            | SuperWord -> (exp_type, FieldAccess3 ("this", "super"), [], [])
            | Var id ->
              (* Look for id in method parameters and local variables. If not found, id is a class attribute. *)
              let (t, v) = find_var_decl_type (m.params @ m.localvars) id in
              if ((compare t Unknown) != 0)
                then (exp_type, Idc3Expr (Var3 (convert_var_id id)), [], [])
              else
                (exp_type, FieldAccess3 ("this", (convert_var_id id)), [], [])
            | CastExp (e, t) ->
              let (e_type, idc3_e, temp_vars, temp_statements) = convert_expression e in
              let (id3_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp idc3_e e_type in
              let type_name = match exp_type with
              | ObjectT c  -> c
              | _ -> failwith "Error: failed to get type name!" in
              (exp_type, CastExp3 (id3_var_name, type_name), temp_vars @ temp_id3_var, temp_statements @ temp_statement)
            | _ -> failwith ("Error: cannot convert expression " ^ (string_of_mOOL_expr exp) ^ " to ir3!")
          end
        | _ -> failwith "Error: expression is not typed!"   
      in

      let convert_statement statement =
        match statement with
        | IfStmt (bool_exp, if_statement_list, else_statement_list) ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression bool_exp in
          let label_num = fresh_label () in
          let (temp_condition_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp new_exp exp_type in
          let if_statement = IfStmt3 (UnaryExp3 (UnaryOp "!", Var3 temp_condition_var_name), label_num) in
          let (inner_if_temp_vars, inner_if_temp_statements) = convert_statement_list if_statement_list in
          let (inner_else_temp_vars, inner_else_temp_statements) = convert_statement_list else_statement_list in
          (temp_vars @ temp_id3_var @ inner_if_temp_vars @ inner_else_temp_vars,
            temp_statements @ temp_statement @ [if_statement] @ inner_if_temp_statements @ [Label3 label_num] @ inner_else_temp_statements)
        | WhileStmt (bool_exp, while_statement_list) ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression bool_exp in
          let start_label_num = fresh_label () in
          let start_label = Label3 start_label_num in
          let end_label_num = fresh_label () in
          let end_label = Label3 end_label_num in
          let end_goto = GoTo3 start_label_num in
          let (temp_condition_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp new_exp exp_type in
          let if_statement = IfStmt3 (UnaryExp3 (UnaryOp "!", Var3 temp_condition_var_name), end_label_num) in
          let (inner_temp_vars, inner_temp_statements) = convert_statement_list while_statement_list in
          (temp_vars @ temp_id3_var @ inner_temp_vars, 
            temp_statements @ temp_statement @ [start_label; if_statement] @ inner_temp_statements @ [end_goto; end_label])
        | ReadStmt var_id ->
          let (t, v) = find_var_decl_type (m.params @ m.localvars) var_id in
          let var_id_string = convert_var_id var_id in
          (* If var id is local, then use it directly. 
             otherwise, create a temp var, assign the attribute value to the temp var, and read from the temp var. *)
          if ((compare t Unknown) != 0)
            then ([], [ReadStmt3 var_id_string])
          else
            let temp_var_name = create_temp_var () in
            ([(t, temp_var_name)], [AssignStmt3 (temp_var_name, FieldAccess3 ("this", var_id_string)); ReadStmt3 temp_var_name])
        | PrintStmt exp ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression exp in
          let (id3_var, temp_id3_var, temp_statement) = create_temp_idc3_for_ir3_exp new_exp exp_type in
          (temp_vars @ temp_id3_var, temp_statements @ temp_statement @ [PrintStmt3 id3_var])
        | AssignStmt (var_id, exp) ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression exp in
          let (t, v) = find_var_decl_type (m.params @ m.localvars) var_id in
          let var_id_string = convert_var_id var_id in
          (* If var id is local, then use it directly. otherwise generate a field assignment statement instead. *)
          if ((compare t Unknown) != 0)
            then (temp_vars, temp_statements @ [AssignStmt3 (var_id_string, new_exp)])
          else
            (temp_vars, temp_statements @ [AssignFieldStmt3 (FieldAccess3 ("this", var_id_string), new_exp)])
        | AssignFieldStmt (exp1, exp2) ->
          let (exp_type1, new_exp1, temp_vars1, temp_statements1) = convert_expression exp1 in
          let (exp_type2, new_exp2, temp_vars2, temp_statements2) = convert_expression exp2 in
          (temp_vars1 @ temp_vars2, temp_statements1 @ temp_statements2 @ [AssignFieldStmt3 (new_exp1, new_exp2)])
        | MdCallStmt exp ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression exp in
          (temp_vars, temp_statements @ [MdCallStmt3 new_exp])
        | ReturnStmt exp ->
          let (exp_type, new_exp, temp_vars, temp_statements) = convert_expression exp in
          let (id3_var_name, temp_id3_var, temp_statement) = create_temp_id3_for_ir3_exp new_exp exp_type in
          (temp_vars @ temp_id3_var, temp_statements @ temp_statement @ [ReturnStmt3 id3_var_name])
        | ReturnVoidStmt -> ([], [ReturnVoidStmt3])
      in
      let new_statements = ref [] in
      let temp_vars = ref [] in
      List.iter(fun statement ->
        let (temp_var_block, new_statement_block) = convert_statement statement in
        new_statements := !new_statements @ new_statement_block;
        temp_vars := !temp_vars @ temp_var_block;
      ) statement_list;
      (!temp_vars, !new_statements) in

      begin
        let (temp_vars, ir3_statements) = convert_statement_list m.stmts in
        (generate_signature m.mOOLid (List.map(fun element -> let x, _ = element in x) m.params), 
          {id3 = convert_var_id m.ir3id;
          rettype3 = m.rettype;
          params3 = (ObjectT cname, "this") :: convert_var_decl_list m.params;
          localvars3 = (convert_var_decl_list m.localvars) @ temp_vars;
          ir3stmts = ir3_statements;
        })
      end in
  let mOOL_class_main_to_IR3 ((cname,mmthd):class_main) (inheritance_table, public_attribute_table, public_method_table, class_methods_table) =
    let (main_method_signature, main_method_ir3) = mOOL_mddecl_to_IR3 cname mmthd inheritance_table public_attribute_table public_method_table class_methods_table in
    ({
      classname = cname;
      parent = None;
      var_table = [];
      meth_table = [(main_method_signature, main_method_ir3.id3)];
      }, main_method_ir3) in
  let mOOL_classes_to_ir3 classes (inheritance_table, public_attribute_table, public_method_table, class_methods_table) =
    let new_classes_ir3 = ref [] in
    let new_classes_methods_ir3 = ref [] in
    List.iter(fun mOOL_class -> 
      let (class_name, parent_name, attributes, methods) = mOOL_class in
      let methods_ir3 = ref [] in
      let mOOL_var_list = ref (List.map(fun (_, x) -> x) attributes) in
      let method_list = ref [] in

      List.iter(fun m ->
        let (method_signature, method_ir3) = mOOL_mddecl_to_IR3 class_name m inheritance_table public_attribute_table public_method_table class_methods_table in
        method_list := !method_list @ [(method_signature, method_ir3.id3)];
        methods_ir3 := !methods_ir3 @ [method_ir3];
      ) methods;

      let rec find_method l m_sig =
        match l with
        | [] -> ("", "")
        | (t_sig, t_id3)::tl ->
          if (compare t_sig m_sig == 0) 
            then (t_sig, t_id3)
          else (find_method tl m_sig) in

      let rec build key =
        if (compare key None != 0)
          then begin
            let attr_list = Hashtbl.find public_attribute_table key in
            let m_list = Hashtbl.find public_method_table key in

            List.iter(fun (var_type, var_id) -> 
              let (x, y) = find_var_decl_type !mOOL_var_list var_id in
              if (compare x Unknown == 0)
                then mOOL_var_list := !mOOL_var_list @ [(var_type, var_id)];
            ) attr_list;

            List.iter(fun m -> 
              let m_signature = generate_signature m.mOOLid (List.map(fun (x, _) -> x) m.params) in
              let (x, y) = find_method !method_list m_signature in
              if (compare x "" == 0)
                then method_list := !method_list @ [(m_signature, convert_var_id m.ir3id)];
            ) m_list;

            build (Hashtbl.find inheritance_table key);
          end in

      build (Hashtbl.find inheritance_table (Some class_name));
      let var_list = List.map(fun (x, y) -> (x, convert_var_id y)) !mOOL_var_list in

      let new_classe_ir3 = {classname = class_name; parent = parent_name; var_table = var_list; meth_table = !method_list} in
      new_classes_ir3 := !new_classes_ir3 @ [new_classe_ir3];
      new_classes_methods_ir3 := !new_classes_methods_ir3 @ !methods_ir3
    ) classes;
    !new_classes_ir3, !new_classes_methods_ir3 in
  let build_table classes =
    let inheritance_table = Hashtbl.create 32 in
    let public_attribute_table = Hashtbl.create 32 in
    let public_method_table = Hashtbl.create 32 in
    let class_methods_table = Hashtbl.create 32 in
    List.iter(fun (class_name, parent_name, attributes, methods) ->
      let this_class = (Some class_name) in
      Hashtbl.add inheritance_table this_class parent_name;
      Hashtbl.add public_attribute_table this_class (List.map(fun (_, x) -> x) (List.filter(fun (x, _) -> (compare x Public == 0)) attributes));
      Hashtbl.add public_method_table this_class (List.filter(fun element -> element.modifier == Public) methods);
      Hashtbl.add class_methods_table (Some class_name) methods;
    ) classes;
    (inheritance_table, public_attribute_table, public_method_table, class_methods_table) in
  begin
    let (inheritance_table, public_attribute_table, public_method_table, class_methods_table) = build_table classes in
    let (newmainir3, newmainmdir3) = mOOL_class_main_to_IR3 mainclass (inheritance_table, public_attribute_table, public_method_table, class_methods_table) in
    let (new_classes_ir3, new_classes_methods_ir3) = mOOL_classes_to_ir3 classes (inheritance_table, public_attribute_table, public_method_table, class_methods_table) in
    (newmainir3::new_classes_ir3, newmainmdir3, new_classes_methods_ir3)
  end
