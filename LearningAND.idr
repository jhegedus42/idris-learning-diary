

list1:List Nat
list1=[1,2,3]
  
list2:List Nat
list2=[1,2,3,4,5]
  
  
total
p1 :Nat-> Type
p1 n = InBounds n list1

total
p2 :Nat-> Type
p2 n = InBounds n list2
  
  
data P1ANDP2:(n:Nat)->Type 
  where MkAnd : {auto ok1:(p1 n)} ->{auto ok2:(p2 n)}->P1ANDP2 n
  
total  
needP1:(n:Nat)->{auto ok:(p1 n)}->String
needP1 n = "OK"
  
test_needP1:String
test_needP1=needP1 1 


test2_needP1:(n:Nat)->{auto ok:P1ANDP2 n}->String
test2_needP1 n {ok=MkAnd}=needP1 n 

data Pointless:(n:Nat)->Type where 

test3_needP1:(n:Nat)->(s:String)->{auto ok2:(p1 n)}->{auto ok:(needP1 n)=s}->String
test3_needP1 n s ="void"

proj_p1 : P1ANDP2 n -> p1 n
proj_p1 (MkAnd {ok1}) = ok1

test4_needP1:(n:Nat)->(s:String)->{auto ok2: P1ANDP2 n}->{auto ok:(needP1 n {ok = proj_p1 ok2})=s}->String -- does not compile, why not, if test3_needP1 and test2_needP1 do ?
test4_needP1 n s ="void"

test5_needP1:(n:Nat)->(s:String)->{auto ok2: P1ANDP2 n}->String 
test5_needP1 n s ="void"
  
check5:String
check5 =test5_needP1 2 "bla"
  

