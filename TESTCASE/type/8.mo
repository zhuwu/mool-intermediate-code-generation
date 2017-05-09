class Main {

Void main(){
 Int t1;
 Int t2;
 return;
 }
}


class A{

 Int t1;
 Int t2;
 Bool b1;
 Void method1(){
 
	Int a;
	return;
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
      

}

class B extends A{
  Int s1;
  Int s2;

  Void method1(){
       Int b;

       return;
  }

  Void method1(Int a){
       Int b;
       A t;

       t = new A() ; 
       t.method1();
       if(b>0){
	t.test_method1(b);
	}
	else{
	  method1();
	}
       t=new B();
       ((D)t).method1();
       method1(3);
       b = a + 1 - s1 * s2;
       return;
  }

  Int method2(){
    Int a;
    a=super.t1;
    //method1(3);
    
    return a;
    }
}

class D {
  
}