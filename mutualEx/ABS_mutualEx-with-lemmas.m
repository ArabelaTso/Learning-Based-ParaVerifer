const 
    NODENUMS : 4;

type 
     state : enum{I, T, C, E};
     NODE: scalarset(NODENUMS);
     
var 
    n : array [NODE] of state;

    x : boolean; 
    
startstate "Init"
for i: NODE do
    n[i] := I; 
endfor;
x := true;
endstartstate;

ruleset i : NODE
do rule "Try"
  n[i] = I 
==> 
begin
  n[i] := T;
endrule;endruleset;

ruleset i : NODE do rule "Crit"
  n[i] = T & x = true 
==>
begin
  n[i] := C; 
  x := false;
endrule;endruleset;

ruleset i : NODE do rule "Exit"
  n[i] = C 
==>
begin
  n[i] := E;
endrule;endruleset;

ruleset i : NODE do rule "Idle"
  n[i] = E 
==> 
  n[i] := I;
  x := true;
endrule;endruleset;

invariant "mutualEx"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i] = E -> n[j] != E
)
 end  end ;


rule "ABS_Crit"
  x = true &
  forall j : NODE do 
  (n[j] != E) & (n[j] != C)
end
==>
x := false;
end;




invariant "rule_1"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i] = C -> n[j] != C
)
 end  end ;




invariant "rule_2"
forall j : NODE do 
x = true -> n[j] != C
 end ;




invariant "rule_3"
forall i : NODE do 
n[i] = C -> x = false
 end ;




invariant "rule_4"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i] = C -> n[j] != E
)
 end  end ;




invariant "rule_5"
forall j : NODE do 
x = true -> n[j] != E
 end ;
