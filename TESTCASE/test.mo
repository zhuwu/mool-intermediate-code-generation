class Main {

Void main(Int i, A abc){
 Int t1;
 Int t2;
 Bool b;
 B a;

 if (i + abc.t1 > a.t2 * 100 || a.b1) {
  t1 = t2 + 9;
 } else {
  a.t1 = t1 * t2;
 }

 while (t2 > 4+t1) {
  a.test_method1(t1, t1 > t2);
  a.test123(a);
  a.t1 = t1;
 }

 a.t1 = t1 * t2 - 5;
 b = (t1 + 5) > (t2 * a.t1);
 a.method2();
 ((A)a).test_method1(t1, (t2 + 5) * (t1 - 10) > 20);
 if (t1 + t2 > 10) {
  a.method1();
 } else {
  t1 = t2 + 5;
 }

 println("abc");
 println(!b);
 println(-t2 + 5 * t1);
 println(-t2 + 5 * (t1 - 10) > 20);
 println(a.t1 + 7);
 println(((A)a).test_method1(t1, (t2 + 5) * (t1 - 10) > 20));
 readln(t2);
 return;
 }
}


class A {

 Int t1;
 Int t2;
 Bool b1;
 Void method1(){
 
	Int a;
	return;
 }

 Int test123(A a) {
  return a.t1;
 }

 A test123(B b) {
  b.method1();
  if (b.method2() > t2) {
    b = NULL;
    test123(b);
  } else {
    test_method1(t1);
  }
  return b;
 }

 Int test_method1(Int c){
     Bool b;
     if (true) {
         return t1 ;
     }
     else { c = t2 ; }
     while (c > 4+t1) {
         c = c + 1 ;
     }
     return t1;
  }
  
  Int test_method1(Int c, Bool a){
     Bool b;
     if (true) {
         return 1;
     }
     else { c = t2 ; }
     while (c > 4+t1) {
         c = c + 1 ;
     }
     return 2;
  }

}

class B extends A{
  //  overriding attribute
  Int t1;
  Int s1;
  Int test2;

  Void method1(){
       Int b;
       //method1(3);
       return;
  }

  Void method1(Int a){
       Int b;
       A t;

       t.method1();
       t.test123((B)t);
       if(b>0){
	t.test_method1(b);
	}
	else{
	  method1();
	}
       //t=new B();
       ((B)t).method1();
       method1(3);
       b = a + 1 - s1 * t1;
       return;
  }

  Int method2(){
    Int a;
    a=super.t1;
    //method1(3);
    
    return a;
    }
}

class C extends B{
  //  overriding attribute
  Int t1;
  Int s1;

  Void method1(){
       Int b;
       //method1(3);
       return;
  }

  Void method1(Int a){
       Int b;
       A t;

       t.method1();
       if(b>0){
  t.test_method1(b);
  }
  else{
    method1();
  }
       //t=new B();
       ((B)t).method1();
       method1(3);
       b = a + 1 - s1 * t1;
       return;
  }

  Int method2(){
    Int a;
    a=super.t1;
    //method1(3);
    test2 = 5;
    
    return a;
    }
}

class D extends B {
  Int t1;
}