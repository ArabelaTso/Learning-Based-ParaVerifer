const 
      NODENUMS : 4;
type 
     location: enum{ M, E, S, I};

     NODE: 1..NODENUMS;

var 
    state : array [NODE] of location;
  
    
ruleset i : NODE do rule "t1"
    state[i] = E ==>
begin
    state[i]  :=  M;
    endrule; endruleset;

      
ruleset i : NODE do rule "t2"
    state[i] = I ==>
begin
  for j: NODE do
      if (j = i) then
        state[j] := S;
      elsif (state[j]=E) then
        state[j] := S;
      elsif (state[j]=M) then
        state[j] := S;
      elsif (state[j]=I) then
        state[j] := I;
      else   
        state[j] := S;
      endif;
  endfor; 
endrule;endruleset;
          

ruleset i : NODE 
do rule "t3"
      state[i] = S ==>
begin
  for j: NODE do
    if (j = i) then
      state[j] := E;
    else   
      state[j] := I;
    endif;
    endfor; 
endrule;endruleset;
      

ruleset i : NODE do rule "t4"
  state[i] = M
==>
begin
  for j: NODE do
      if (j = i) then
            state[j] := E ;
      else   
            state[j] := I;
      endif;
  endfor; 
endrule;
endruleset;

startstate
begin
 for i: NODE do
    state[i]  :=  I; 
  endfor; 
endstartstate;

invariant "Mesi"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (state[i] = M -> state[j] != M
)
 end  end ;



rule "ABS_t2"
  True
==>
for j: NODE do
      if (False) then
        state[j] := S;
 elsif (state[j]=E) then
        state[j] := S;
 elsif (state[j]=M) then
        state[j] := S;
 elsif (state[j]=I) then
        state[j] := I;
 else   
        state[j] := S;
 endif;
 endfor;
end;



rule "ABS_t3"
  forall j : NODE do 
    state[j] != M &
    state[j] != E 
  end
==>
for j: NODE do
    if (False) then
      state[j] := E;
 else   
      state[j] := I;
 endif;
 endfor;
end;



rule "ABS_t4"
  forall j : NODE do 
    state[j] != M &
    state[j] != S &
    state[j] != E 
  end
==>
for j: NODE do
      if (False) then
            state[j] := E;
 else   
            state[j] := I;
 endif;
 endfor;
end;
