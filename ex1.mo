/* 
   Sample test 1
 */

class Main {

Void main(Int i, Int a, Int b,Int d){
  Int t1;
  Int t2;
  return ;
 }
}

class DummyP{
  Int i;
}

class Dummy extends DummyP{

  Int i;
  Dummy j;

private Int dummy() {
   Bool i;
   Bool j;

   if (i || j) {
          return 1;
   }
   else {
     while(i) {
       i = !j;
     }
            return 2;
   }    
}

Int getCompute() {
   DummyP a; 
   Dummy d;

   d = (Dummy)a;
   // d = a;
   a = (DummyP) d;
   return 1; 
}

}
