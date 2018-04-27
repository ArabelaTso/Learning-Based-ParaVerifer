const 
      NODENUMS : 2;
	dataNums: 2;
			
type 
     state : enum{I, T, C, E};

     DATA: 1..dataNums;

     status : record st:state; data: DATA; end;
     
     NODE: 1..NODENUMS;

var 
    n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;
    

ruleset i : NODE do
rule "Try" 
      n[i].st = I 
==>
begin
      n[i].st := T;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = T & 
      x = true 
==>
begin
      n[i].st := C; x := false; 
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = C 
==>
begin
      n[i].st := E;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = E 
==>
begin 
      n[i].st := I;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; data : DATA do rule "Store"
	n[i].st = C
==>
begin
      n[i].st := C; 
      x := false; 
      auxDATA := data; 
      n[i].data := data; 
endrule;endruleset;    

ruleset d : DATA do 
startstate
begin
 for i: NODE do
    n[i].st := I; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endstartstate;
endruleset;


ruleset i: NODE; j: NODE do
invariant "CntrlProp"
  i != j -> (n[i].st = C -> n[j].st != C);
endruleset;

ruleset i:NODE  do 
invariant "DataProp"

  (n[i].st= C -> n[i].data =auxDATA);
endruleset;


ruleset data: DATA do rule "ABS_Store"
   
  forall j : NODE do 
  (n[j].st != C) & (n[j].st != E)
end
==>x := false;
 auxDATA := data;
end;end;



rule "ABS_Crit"
  x = true
==>
x := false;
end;



rule "ABS_Idle"
   
  forall j : NODE do 
  (n[j].st != C) & (n[j].st != E)
end
==>
x := true;
 memDATA := auxDATA;
end;


invariant "rule_1"
forall i : NODE do 
n[i].st = E -> n[i].data = auxDATA
 end ;



invariant "rule_2"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i].st = E -> n[j].st != E
)
 end  end ;




invariant "rule_3"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i].st = E -> n[j].st != C
)
 end  end ;

