data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))
  
parity : (n:Nat) -> Parity n
parity Z = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even ?= Even {n=S j}
  parity (S (S (S (j + j)))) | Odd  ?=  Odd {n=S j}  
  
parity_lemma_1 j value = rewrite plusSuccRightSucc (S j) j in value
  
parity_lemma_2 j value = rewrite plusSuccRightSucc (S j) j in value
 
-- Safe divide 

--total
--can_I_divide_by_this_number: Nat ->  Type
--can_I_divide_by_this_number (S n) =  Unit
--can_I_divide_by_this_number     Z =  Void

data CanDivideBy : Nat -> Type
  where YesICan : CanDivideBy (S k)
 
data AreYouSure : (n:Nat)->Type  
  where YesIamSure : {auto ok:CanDivideBy n}->AreYouSure n
  
divisor1 : CanDivideBy 1
divisor1 = YesICan

--divisor0 : CanDivideBy 0
--divisor0 = YesICan
  
total  
safeDivide: (a:Nat) -> (b:Nat) ->{auto ok:AreYouSure b}->Double 
safeDivide a b = (cast $ a)/(cast $ b)
 
--test:(a:Nat)->Type
--test b=a
    
half:Double
half=safeDivide 1 2

--bad:Double
--bad=safeDivide 1 0

total
isZero : (n: Nat) -> Bool 
isZero Z = True
isZero (S m) = False

total
isZero' : (n: Nat)->{auto ok: CanDivideBy n} -> Bool 
isZero' (S m) {ok=YesICan}= False


--trouble:Double
--trouble=safeDivide 1 0

data Row = R1 | R2 | R3

data Col = C1 | C2 | C3 

data Location = OnBoard Row Col | OffBoard
  
data Color = Green | Blue | Red 

total 
coloredRows:Row -> List Color 
coloredRows R1 = [Green]
coloredRows R2 = [Blue,  Red]
coloredRows R3 = [Green, Green]

total
getNatIndex : Col-> Nat
getNatIndex C1 = 0
getNatIndex C2 = 1
getNatIndex C3 = 2

total
inbounds :Row->Col-> Type
inbounds r c = InBounds (getNatIndex c) (coloredRows r)

total
isLocInBounds: Location -> Type
isLocInBounds (OnBoard r c )= inbounds r c
isLocInBounds (OffBoard) = Void

inbound_location_example:Location
inbound_location_example = OnBoard R1 C1

notinbound_location_example:Location
notinbound_location_example = OnBoard R1 C2

total
accept_only_inbound_locations:(l:Location)->{auto ok: isLocInBounds l}->String
accept_only_inbound_locations l = "Accepted"
     
accept_inbound_example:String
accept_inbound_example = accept_only_inbound_locations inbound_location_example    
       
--does not compile, as expected
--reject_outbound_example:String
--reject_outbound_example = accept_only_inbound_locations notinbound_location_example   

data IsOnBoard:(l:Location) ->Type  
  where ItIs: IsOnBoard(OnBoard r w)
  
accept_only_onboard:(l:Location)->{auto ok:IsOnBoard l }->String
accept_only_onboard l = "Accepted"

accept_onboard_example1:String
accept_onboard_example1=accept_only_onboard inbound_location_example

accept_onboard_example2:String
accept_onboard_example2=accept_only_onboard notinbound_location_example

off_board_location_example:Location
off_board_location_example= OffBoard

-- does not compile, as expected
--reject_off_board_example:String
--reject_off_board_example=accept_only_onboard off_board_location_example

-- so far so good
-- here comes the problem :

data IsOnBoardAndInBound:(l:Location)->Type
  --where YesBothAreTrue: {auto ok2:(OnBoard r w)=l}->{auto ok1:isLocInBounds l}->IsOnBoardAndInBound l -- works too
  where YesBothAreTrue: (ok2:(OnBoard r w)=l)->(ok:isLocInBounds l)->IsOnBoardAndInBound l -- works too
  --where YesBothAreTrue: {auto ok:isLocInBounds (OnBoard r w)} -> IsOnBoardAndInBound (OnBoard r w)

--data IsOnBoardAndInBound2(l:Location)->Type 
--  where YesBothAreTrue2: Pair (OnBoard r w) ()
   
accept_only_inbound_and_onboard:(l:Location)
   ->{auto ok:IsOnBoardAndInBound l}
--   ->{auto ok2:(accept_only_inbound_locations l)="Accepted"} -- uncomment this and the code does not compile anymore
   ->String
accept_only_inbound_and_onboard l = "Accepted" 
-- Is this a limitation in Idris ? 
-- I think this should compile 
-- but it does not, why not ? How can this be fixed ?
-- Because if the first auto can be filled in then 
-- the second equality should follow from the first one, 
-- but Idris cannot proove that. What am I missing here?
  
    
check1:String 
check1 = accept_only_inbound_and_onboard inbound_location_example
--check1 = accept_only_inbound_and_onboard notinbound_location_example
--check1 = accept_only_inbound_and_onboard off_board_location_example 

check2:(l:Location)->{auto ok:IsOnBoardAndInBound l}->String
check2 l {ok=YesBothAreTrue ok2 ok1} =accept_only_inbound_locations l -- same problem with this one

