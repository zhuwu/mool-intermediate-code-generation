
(* ==================================================== *)
(* ============== CS4212 Compiler Design ============== *)
(*   	       Static Check of mOOL programs            *)
(* ==================================================== *)

open MOOL_structs

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

(* Get upper bound of two types. If any one of the type is VoidT, define upper bound to VoidT. *)
let find_upper_bound inheritance_table t1 t2 =
  let rec build_parents parent_list class_name =
    let parent = Hashtbl.find inheritance_table class_name in
    if ((compare parent None) != 0)
      then begin
        build_parents (parent::parent_list) parent
      end
    else
      parent_list in
  match (t1, t2) with
  | VoidT, _
  | _, VoidT -> VoidT
  | IntT, IntT -> IntT
  | BoolT, BoolT -> BoolT
  | StringT, StringT -> StringT
  | ObjectT c1, ObjectT c2 ->
    if ((String.compare c1 c2) == 0 || (String.compare c2 "null") == 0)
      then t1
    else
      if (String.compare c1 "null" == 0)
        then t2
      else begin
        let t1_parents = build_parents [(Some c1)] (Some c1) in
        let t2_parents = build_parents [(Some c2)] (Some c2) in
        let last_match = ref None in
        List.iter(fun p_t1 ->
          let is_common = List.exists(fun p_t2 -> compare p_t1 p_t2 == 0) t2_parents in
          if (is_common)
            then last_match := p_t1;
        ) t1_parents;
        match !last_match with
        | Some c -> ObjectT c
        | _ -> Unknown
      end
  | _, _ -> Unknown

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

(* Check whether every item in list is unique *)
let rec check_unique_list l =
  match l with
  | [] -> true
  | hd::tl -> let result = List.exists(fun x -> compare x hd == 0) tl in
      if (result) then false 
      else check_unique_list tl

let check_type inheritance_table type_list =
  List.iter(fun var_type -> 
    match var_type with
    | IntT -> ()
    | BoolT -> ()
    | StringT -> ()
    | ObjectT class_name -> 
      if (not (Hashtbl.mem inheritance_table (Some class_name)))
        then failwith ("Unknown type detected! " ^ class_name)
    | VoidT -> ()
    | Unknown -> failwith "Unknown type detected!"
  ) type_list;
  ()

(* Find the declared type of a variable *)    
let rec find_var_decl_type var_list var_id =
  match var_list with
  | [] -> (Unknown, var_id)
  | (t,v)::tl ->
    if (compare_var_ids v var_id) 
      then (t,v)
    else (find_var_decl_type tl var_id)

(* Annotate variable declarations with scope *)
let create_scoped_var_decl var_list scope =
  List.map(fun element -> 
    let (var_type, var_id) = element in
    match var_id with
    | SimpleVarId id -> (var_type, TypedVarId (id, var_type, scope))
    | TypedVarId (id, typed_var_type, typed_scope) -> (var_type, TypedVarId(id, var_type, scope))
  ) var_list

(* check whether class 1 is inherited from class 2 *)
let rec check_inheritance inheritance_table class_1 class_2 =
  if ((compare class_1 None == 0) || (compare class_2 None == 0))
    then false
  else
    begin
      let class_1_parent = Hashtbl.find inheritance_table class_1 in
      if (compare class_1_parent class_2 == 0) 
        then true
      else check_inheritance inheritance_table class_1_parent class_2
    end

let rec find_public_attribute class_descriptor class_public_attributes_table class_name id =
  if (compare class_name None == 0)
    then failwith "Error: illegal attribute access!"
  else begin
    let attribute_list = Hashtbl.find class_public_attributes_table class_name in
    let result_list = List.filter(fun element ->
      let (attribute_type, attribute_id) = element in
      (compare_var_ids attribute_id id)
    ) attribute_list in
    if (List.length result_list > 0)
      then List.hd result_list
    else
      let parent = Hashtbl.find class_descriptor class_name in
      find_public_attribute class_descriptor class_public_attributes_table parent id
  end

let rec find_method_decl inheritance_table class_public_methods_table current_class_methods class_name method_name param_type_list =
  let method_list = ref [] in
  method_list := current_class_methods @ !method_list;
  let rec build_method_list c =
    if (compare c None != 0)
      then begin
        method_list := !method_list @ (Hashtbl.find class_public_methods_table c);
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
    failwith ("Error: illegal method call " ^ (string_of_var_id method_name) ^ "!")

let rec check_this exp =
  match exp with
  | ThisWord -> "this"
  | CastExp (e, t) -> check_this e
  | _ -> "other"

(* Check method declariation *)
let type_check_method class_descriptor class_public_attributes_table class_public_methods_table class_methods_table environment class_name method_decl =
  let scoped_environment = (create_scoped_var_decl method_decl.localvars 2) @ (create_scoped_var_decl method_decl.params 2) @ environment in
  let method_return_type = method_decl.rettype in
  let rec type_check_expression expression =
    match expression with
    | UnaryExp (op, exp) ->
      let (exp_type, new_exp) = type_check_expression exp in
      begin
        match (op, exp_type) with
        | (UnaryOp operator, BoolT) ->
          if (compare operator "!" == 0)
            then (BoolT, TypedExp (UnaryExp (op, new_exp), BoolT))
          else
            failwith "Error: '-' can only be applied to int expression!"
        | (UnaryOp operator, IntT) ->
          if (compare operator "-" == 0)
            then (IntT, TypedExp (UnaryExp (op, new_exp), IntT))
          else
            failwith "Error: '!' can only be applied to bool expression!" 
        | (_,_) -> failwith "Error: unary operator check failed!"
      end
    | BinaryExp (op, exp1, exp2) -> 
      let (exp_type1, new_exp1) = type_check_expression exp1 in
      let (exp_type2, new_exp2) = type_check_expression exp2 in
      begin
        match (op, exp_type1, exp_type2) with
        | (RelationalOp operator, IntT, IntT) -> (BoolT, TypedExp (BinaryExp (op, new_exp1, new_exp2), BoolT))
        | (AritmeticOp operator, IntT, IntT) -> (IntT, TypedExp (BinaryExp (op, new_exp1, new_exp2), IntT))
        | (BooleanOp operator, BoolT, BoolT) -> (BoolT, TypedExp (BinaryExp (op, new_exp1, new_exp2), BoolT))
        | (_, _, _) -> failwith "Error: operation is not allowed!"
      end
    | FieldAccess (exp, id) ->
      let e_t = check_this exp in
      let (exp_type, new_exp) = type_check_expression exp in
      if (compare e_t "this" == 0 && compare_mOOL_types exp_type (ObjectT class_name)) then
        let (v_type, v_id) = (find_var_decl_type scoped_environment id) in
        if (not (compare_mOOL_types v_type Unknown)) then
          match v_id with
          | TypedVarId (_, _, scope) ->
            if (scope <= 1) then
              (v_type, TypedExp (FieldAccess (new_exp, id), v_type))
            else
              failwith ("Error: illegal access to attribute " ^ (string_of_var_id id) ^ "!")
          | _ -> failwith ("Error: illegal access to attribute " ^ (string_of_var_id id) ^ "!")
        else
          failwith ("Error: illegal access to attribute " ^ (string_of_var_id id) ^ "!")
      else
        begin
          match exp_type with
          | ObjectT class_name ->
            let (id_type, _) = find_public_attribute class_descriptor class_public_attributes_table (Some class_name) id in
            (id_type, TypedExp (FieldAccess (new_exp, id), id_type))
          | _ -> failwith ("Error: illegal access to attribute " ^ (string_of_var_id id) ^ "!")
        end
    | ObjectCreate c -> 
      if (Hashtbl.mem class_descriptor (Some c))
        then ((ObjectT c), TypedExp (expression, (ObjectT c)))
      else
        failwith ("Error: initialize object of unknown classs " ^ c)
    | MdCall (exp, param_list) -> 
      let new_param_list = List.map(fun element -> type_check_expression element) param_list in
      let param_exp_list = List.map(fun element -> let (_, x) = element in x) new_param_list in
      let param_type_list = List.map(fun element -> let (x, _) = element in x) new_param_list in
      begin
        match exp with
        | FieldAccess (object_exp, method_name) ->
          let (object_type, object_new_exp) = (type_check_expression object_exp) in
          let o_t = check_this object_exp in
          begin
            match object_type with
            | ObjectT c ->
              let method_decl =
                if (compare o_t "this" == 0 && compare_mOOL_types object_type (ObjectT class_name))
                  then begin
                    let class_option = (Some class_name) in
                    let current_class_methods = Hashtbl.find class_methods_table class_option in
                    find_method_decl class_descriptor class_public_methods_table current_class_methods class_option method_name param_type_list
                  end
                else
                  let class_option = (Some c) in
                  let current_class_methods = Hashtbl.find class_public_methods_table class_option in
                  find_method_decl class_descriptor class_public_methods_table current_class_methods class_option method_name param_type_list in
              (method_decl.rettype, TypedExp (MdCall (FieldAccess (object_new_exp, method_name), param_exp_list), method_decl.rettype))
            | _ -> failwith ("Error: illegal method call " ^ (string_of_mOOL_expr expression) ^ "!")
          end
        | Var method_name ->
          let class_option = (Some class_name) in
          let current_class_methods = Hashtbl.find class_methods_table class_option in
          let method_decl = find_method_decl class_descriptor class_public_methods_table current_class_methods class_option method_name param_type_list in
          (method_decl.rettype, TypedExp (MdCall (Var method_name, param_exp_list), method_decl.rettype))
        | _ -> failwith ("Error: illegal method call " ^ (string_of_mOOL_expr expression) ^ "!")
      end
    | BoolLiteral b -> (BoolT, TypedExp (expression, BoolT))
    | IntLiteral i -> (IntT, TypedExp (expression, IntT))
    | StringLiteral s -> (StringT, TypedExp (expression, StringT))
    | ThisWord ->
      if (Hashtbl.mem class_descriptor (Some class_name))
        then ((ObjectT class_name), TypedExp (expression, (ObjectT class_name)))
      else
        failwith ("Error: illegal 'this' for class " ^ class_name)
    | NullWord -> ((ObjectT "null"), TypedExp (expression ,(ObjectT "null")))
    | SuperWord ->
      begin
        let parent = Hashtbl.find class_descriptor (Some class_name) in
        match parent with
        | Some super_class -> ((ObjectT super_class), TypedExp (expression, (ObjectT super_class)))
        | None -> failwith ("Error: class " ^ class_name ^ " does not have parent!")
      end
    | Var v -> 
      let (v_type, v_id) = (find_var_decl_type scoped_environment v) in
      if (compare_mOOL_types v_type Unknown)
        then failwith ("Error: " ^ (string_of_var_id v_id) ^ " is not defined!")
      else
        (v_type, TypedExp (Var v_id, v_type))
    | CastExp (exp, t) ->
      let (exp_type, new_exp) = type_check_expression exp in
      if (compare_mOOL_types t exp_type)
        then (t, TypedExp (CastExp (new_exp, t), t))
      else
        begin
          let target_class_name =
            match t with
            | ObjectT class_name -> class_name
            | _ -> failwith "Error: types are not matched during casting!" in
          let original_class_name =
            match exp_type with
            | ObjectT class_name -> class_name
            | _ -> failwith "Error: types are not matched during casting!" in
          if ((check_inheritance class_descriptor (Some target_class_name) (Some original_class_name)) 
            || (check_inheritance class_descriptor (Some original_class_name) (Some target_class_name)))
            then (t, TypedExp (CastExp (new_exp, t), t))
          else
            failwith "Error: types are not matched during casting!"
        end
    | TypedExp (exp, t) -> (t, expression) in
  let rec type_check_statement_list statements statements_type =
    let check_statement statement =
      match statement with
      | ReturnVoidStmt ->
        if (not (compare_mOOL_types method_return_type VoidT))
          then failwith ("Error: method has illegal return type!")
        else
          (VoidT, statement)
      | ReturnStmt e ->
        let (exp_type, new_exp) = type_check_expression e in
        if (not (compare_mOOL_types_with_inheritance class_descriptor method_return_type exp_type))
          then failwith "Error: method has illegal return type!"
        else
          (exp_type, ReturnStmt new_exp)
      | MdCallStmt e ->
        let (exp_type, new_exp) = type_check_expression e in
        (VoidT, MdCallStmt new_exp)
      | AssignFieldStmt (e1, e2) ->
        let (exp_type1, new_exp1) = type_check_expression e1 in
        let (exp_type2, new_exp2) = type_check_expression e2 in
        if (not (compare_mOOL_types_with_inheritance class_descriptor exp_type1 exp_type2))
          then failwith "Error: type missmatch when assigning value to an attribute!"
        else
          (VoidT, AssignFieldStmt (new_exp1, new_exp2))
      | AssignStmt (var, e) ->
        let (exp_type, new_exp) = type_check_expression e in
        let (var_type, var_id) = find_var_decl_type scoped_environment var in
        if (not (compare_mOOL_types_with_inheritance class_descriptor var_type exp_type))
          then failwith "Error: type missmatch when assigning value to an variable!"
        else
          (VoidT, AssignStmt (var_id, new_exp))
      | PrintStmt e ->
        let (exp_type, new_exp) = type_check_expression e in
        if ((compare_mOOL_types exp_type IntT) || (compare_mOOL_types exp_type BoolT) || (compare_mOOL_types exp_type StringT))
          then (VoidT, PrintStmt new_exp)
        else
          failwith "Error: illegal print!"
      | ReadStmt id ->
        let (id_type, annotated_id) = find_var_decl_type scoped_environment id in
        if ((compare_mOOL_types id_type IntT) || (compare_mOOL_types id_type BoolT) || (compare_mOOL_types id_type StringT))
          then (VoidT, ReadStmt annotated_id)
        else
          failwith "Error: illegal read!"
      | WhileStmt (e, while_statements) ->
        let (exp_type, new_exp) = type_check_expression e in
        if (not (compare_mOOL_types exp_type BoolT))
          then failwith "Error: illegal while condition!"
        else begin
          let (while_statements_type, new_while_statements) = type_check_statement_list while_statements VoidT in
          (while_statements_type, WhileStmt (new_exp, new_while_statements))
        end
      | IfStmt (e, if_statements, else_statements) ->
        let (exp_type, new_exp) = type_check_expression e in
        if (not (compare_mOOL_types exp_type BoolT))
          then failwith "Error: illegal if condition!"
        else begin
          let (if_statements_type, new_if_statements) = type_check_statement_list if_statements VoidT in
          let (else_statements_type, new_else_statements) = type_check_statement_list else_statements VoidT in
          let new_if_else = IfStmt (new_exp, new_if_statements, new_else_statements) in
          let if_else_upper_bound = find_upper_bound class_descriptor if_statements_type else_statements_type in
          match if_else_upper_bound with
          | Unknown -> failwith "Error: different types are returned in if and else!"
          | _ -> (if_else_upper_bound, new_if_else)
        end in
    let length = List.length statements in
    let counter = ref 0 in
    let new_statements = ref [] in
    let statements_type = ref VoidT in
    List.iter(fun statement ->
      counter := !counter + 1;
      let (statement_type, new_statement) = check_statement statement in
      new_statements := !new_statements @ [new_statement];
      if (!counter == length)
        then statements_type := statement_type;
    ) statements;
    (!statements_type, !new_statements) in
  let (new_statements_type, new_statement_list) = (type_check_statement_list method_decl.stmts VoidT) in
  if (compare_mOOL_types_with_inheritance class_descriptor method_return_type new_statements_type)
    then {method_decl with stmts = new_statement_list}
  else
    failwith "Error: method return type missmatch!"
  
    
(* TypeCheck a MOOL Program. 
   Return a new MOOL Program where expressions are annotated with types
 *)
let type_check_mOOL_program (p:mOOL_program) : mOOL_program =
  (* Check whether class names are unique *)
  let type_check_unique_class_name main_class classes = 
    let main_class_name, _ = main_class in
    let class_name_list = [main_class_name] @ List.map(fun element -> let x, _, _, _ = element in x) classes in
    let result = check_unique_list class_name_list in
    if (result) then true
    else failwith "Error: class names are not unique!" in
  (* Check whether program has cyclic inheritance *)
  let type_check_acyclic_hierachy classes =
    let table = Hashtbl.create 32 in
    List.iter(fun element -> 
      let (class_name, parent, _, _) = element in
      Hashtbl.add table (Some class_name) parent) classes;
    let checking_table = Hashtbl.create 32 in
    let rec check key value init=
      let () = if (init) then begin
        Hashtbl.reset checking_table;
        Hashtbl.add checking_table key key
      end in
      if (compare value None == 0) then ()
      else begin
        if (Hashtbl.mem checking_table value) then failwith "Cyclic class hierachy detected!"
        else begin
          Hashtbl.add checking_table value value;
          check key (Hashtbl.find table value) false
        end
      end in
    Hashtbl.iter(fun class_name parent -> check class_name parent true) table;
    table in
  (* Check for unique identifiers in scope and method overloading *)
  let type_check_identifers_and_methods inheritance_table main_class classes =
    let (_, main_method) = main_class in
    let main_method_param_names = List.map(fun element -> let _, x = element in x) main_method.params in
    let main_method_local_var_names = List.map(fun element -> let _, x = element in x) main_method.localvars in
    let main_method_param_types = List.map(fun element -> let x, _ = element in x) main_method.params in
    let main_method_local_var_types = List.map(fun element -> let x, _ = element in x) main_method.localvars in
    check_type inheritance_table main_method_param_types;
    check_type inheritance_table main_method_local_var_types;

    if (not (check_unique_list (main_method_param_names @ main_method_local_var_names)))
      then failwith "Error: main method parameter names and local variable names are not unique!";

    let class_method_table = Hashtbl.create 32 in
    let class_public_attributes_table = Hashtbl.create 32 in
    let class_public_methods_table = Hashtbl.create 32 in
    let class_methods_table = Hashtbl.create 32 in
    List.iter(fun class_body ->
      let (class_name, _, attribute_list, method_list) = class_body in
      let attribute_names = List.map(fun element -> let _, (_, x) = element in x) attribute_list in
      let attribute_types = List.map(fun element -> let _, (x, _) = element in x) attribute_list in
      check_type inheritance_table attribute_types;
      if (not (check_unique_list attribute_names)) 
        then failwith "Error: class attribute names are not unique!";

      let method_counter = ref 0 in
      let signature_list = ref [] in
      List.iter(fun class_method ->
        class_method.ir3id <- SimpleVarId ("_" ^ class_name ^ "_" ^ (string_of_int !method_counter));
        method_counter := !method_counter + 1;
        let {mOOLid = method_name; ir3id = _; modifier = _; rettype = return_type; params = param_list; localvars = local_var_list; stmts = _} = class_method in
        check_type inheritance_table [return_type];

        let params_names = List.map(fun element -> let _, x = element in x) param_list in
        let local_var_names = List.map(fun element -> let _, x = element in x) local_var_list in
        let param_types = List.map(fun element -> let x, _ = element in x) param_list in
        let local_var_types = List.map(fun element -> let x, _ = element in x) local_var_list in
        check_type inheritance_table param_types;
        check_type inheritance_table local_var_types;
        if (not (check_unique_list (params_names @ local_var_names))) 
          then failwith "Error: method parameter names and local variable names are not unique!"
        else begin
          signature_list := (method_name, param_types) :: !signature_list
        end
        (*if (not (check_unique_list params_names)) then failwith "Error: method parameter names are not unique!"
        else begin
          let local_var_names = List.map(fun element -> let _, x = element in x) local_var_list in
          if (not (check_unique_list local_var_names)) then failwith "Error: method local variable names are not unique!"
          else begin
            let params_types = List.map(fun element -> let x, _ = element in x) param_list in
            signature_list := (method_name, params_types) :: !signature_list
          end
        end*)
      ) method_list;
      if (not (check_unique_list !signature_list)) 
        then failwith "Error: signatures of methods in the same class are not unique!";

      let method_signature_return_type_list = List.map(fun element ->
        let {mOOLid = method_name; ir3id = _; modifier = _; rettype = return_type; params = param_list; localvars = _; stmts = _} = element in
        let params_types = List.map(fun element -> let x, _ = element in x) param_list in
        (method_name, return_type, params_types)
      ) method_list in
      Hashtbl.add class_method_table (Some class_name) method_signature_return_type_list;

      Hashtbl.add class_public_attributes_table (Some class_name) 
        (List.map(fun element -> let _, x = element in x) (List.filter(fun element -> let x, _ = element in x == Public) attribute_list));
      Hashtbl.add class_public_methods_table (Some class_name) (List.filter(fun element -> element.modifier == Public) method_list);
      Hashtbl.add class_methods_table (Some class_name) method_list;
    ) classes;
    
    let rec check key value =
      if (compare value None == 0) then ()
      else begin
        let current_class_methods = Hashtbl.find class_method_table key in
        let parent_class_methods = Hashtbl.find class_method_table value in
        List.iter(fun element -> 
          let (method_name, return_type, params_types) = element in
          List.iter(fun parent_element -> 
            let (parent_method_name, parent_return_type, parent_params_types) = parent_element in
            if ((compare method_name parent_method_name == 0) && (compare params_types parent_params_types == 0) 
              && (compare return_type parent_return_type != 0)) then failwith "Error: illegal overriding!";
            ()
          ) parent_class_methods;
        ) current_class_methods;
        check key (Hashtbl.find inheritance_table value)
      end in
    Hashtbl.iter(fun class_name parent -> check class_name parent) inheritance_table;
    (class_public_attributes_table, class_public_methods_table, class_methods_table) in
  (* Transform main class *)
  let transform_main inheritance_table class_public_attributes_table class_public_methods_table class_methods_table main_class = 
    let (class_name, method_decl) = main_class in
    (class_name, 
      (type_check_method inheritance_table class_public_attributes_table class_public_methods_table class_methods_table [] class_name method_decl)) in
  (* Transform classes *)
  let transform_classes inheritance_table class_public_attributes_table class_public_methods_table class_methods_table classes =
    List.map(fun c -> 
      let (class_name, parent, attributes, methods) = c in
      let environment = ref (create_scoped_var_decl (List.map(fun element -> let (_, x) = element in x) attributes) 1) in
      let rec build_environment c_name =
        if ((compare c_name None) != 0)
          then begin
            environment := !environment @ (create_scoped_var_decl (Hashtbl.find class_public_attributes_table c_name) 0);
            build_environment (Hashtbl.find inheritance_table c_name);
          end in
      build_environment (Hashtbl.find inheritance_table (Some class_name));
      let new_methods = List.map(fun m ->
        type_check_method inheritance_table class_public_attributes_table class_public_methods_table class_methods_table !environment class_name m
      ) methods in
      (class_name, parent, attributes, new_methods)
    ) classes in 

begin
  let (main_class, classes) = p in
  let _ = type_check_unique_class_name main_class classes in
  let inheritance_table = type_check_acyclic_hierachy classes in
  let (class_public_attributes_table, class_public_methods_table, class_methods_table) =
    type_check_identifers_and_methods inheritance_table main_class classes in
  let new_main_class = 
    transform_main inheritance_table class_public_attributes_table class_public_methods_table class_methods_table main_class in
  let new_classes = transform_classes inheritance_table class_public_attributes_table class_public_methods_table class_methods_table classes in
  (new_main_class, new_classes)
end
