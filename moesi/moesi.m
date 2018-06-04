const 
    num_NODEs : 2;

type 
    NODE : 1..num_NODEs;
    locationType: enum{M, OSTATUS, E, S, I};

var 
    a : array[NODE] of locationType;

ruleset i : NODE do
rule "rule_t1"
    a[i] = E ==>
begin
    a[i] := M;
endrule;endruleset;

ruleset i : NODE do
rule "rule_t2"
    a[i] = I ==>
begin
    for j: NODE do
        if (j = i)
            then a[j] := S;
        elsif (a[j] = E)
            then a[j] := S;
        elsif (a[j] = M)
            then a[j] := OSTATUS;
        else a[j] := a[j];
        endif;
        endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "rul_t3"
    a[i] = S ==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "rul_t4"
    a[i] = OSTATUS
==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;endruleset;

ruleset i : NODE do
rule "rul_t5"
    a[i] = I ==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;
endruleset;

startstate
begin
 for i: NODE do
    a[i] := I; 
  endfor; 
endstartstate;


invariant "Moesi"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (a[i] = M -> a[j] != M
)
 end  end ;


