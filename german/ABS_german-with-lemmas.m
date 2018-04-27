
const

  NODE_NUM : 3;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum{I,S,E};

  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;

  MSG_CMD : enum{Empty,ReqS,ReqE,Inv,InvAck,GntS,GntE};

  MSG : record
    Cmd : MSG_CMD;
    Data : DATA;
  end;
  new_type_0 : array [ NODE ] of CACHE;
  new_type_1 : array [ NODE ] of MSG;
  new_type_2 : array [ NODE ] of MSG;
  new_type_3 : array [ NODE ] of MSG;
  new_type_4 : array [ NODE ] of boolean;
  new_type_5 : array [ NODE ] of boolean;

var

  Cache : new_type_0;
  Chan1 : new_type_1;
  Chan2 : new_type_2;
  Chan3 : new_type_3;
  InvSet : new_type_4;
  ShrSet : new_type_5;
  ExGntd : boolean;
  CurCmd : MSG_CMD;
  CurPtr : ABS_NODE;
  MemData : DATA;
  AuxData : DATA;

ruleset  i : NODE do
rule "RecvGntE1"
  Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvGntS2"
  Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntE3"
  CurCmd = ReqE &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false &
  forall j : NODE do
    ShrSet[j] = false
  end
==>
begin
  Chan2[i].Cmd := GntE;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntS4"
  CurCmd = ReqS &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck5"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
  ExGntd := false;
  MemData := Chan3[i].Data;
  undefine Chan3[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck6"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd != true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck7"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State = E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Chan3[i].Data := Cache[i].Data;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck8"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State != E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv9"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqE
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv10"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqS &
  ExGntd = true
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqE11"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqS12"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE13"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE14"
  Chan1[i].Cmd = Empty &
  Cache[i].State = S
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqS15"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;

ruleset  d : DATA; i : NODE do
rule "Store16"
  Cache[i].State = E
==>
begin
  Cache[i].Data := d;
  AuxData := d;
endrule;
endruleset;

ruleset  d : DATA do
startstate
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  ExGntd := false;
  CurCmd := Empty;
  MemData := d;
  AuxData := d;
endstartstate;
endruleset;
invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
      (i != j ->
      ((Cache[i].State = E ->
      Cache[j].State = I) &
      (Cache[i].State = S ->
      (Cache[j].State = I |
      Cache[j].State = S))))
    end
  end;

invariant "DataProp"
  ((ExGntd = false ->
  MemData = AuxData) &
  forall i : NODE do
    (Cache[i].State != I ->
    Cache[i].Data = AuxData)
  end);




rule "ABS_SendGntE3"
  CurPtr = Other & ExGntd = false & forall j : NODE do
    ShrSet[j] = false
  end & CurCmd = ReqE & MemData = AuxData &
  forall j : NODE do 
  (Chan2[j].Cmd != GntE) & (Cache[j].State != E)
end
==>
ExGntd := true;
 CurCmd := Empty;
 undefine CurPtr;
end;



rule "ABS_SendGntS4"
  CurPtr = Other & ExGntd = false & MemData = AuxData & CurCmd = ReqS &
  forall j : NODE do 
  (Chan2[j].Cmd != GntE) & (Cache[j].State != E)
end
==>
CurCmd := Empty;
 undefine CurPtr;
end;



rule "ABS_RecvInvAck5"
  CurCmd != Empty & ExGntd = true &
  forall j : NODE do 
  (Chan2[j].Cmd != GntE) & (Cache[j].State = I) & (Chan2[j].Cmd != GntS) & (ShrSet[j] = false) & (Chan3[j].Cmd = Empty) & (Chan3[j].Cmd != InvAck) & (Cache[j].State != E) & (InvSet[j] = false) & (Chan2[j].Cmd != Inv) & (Chan2[j].Cmd = Empty) & (Cache[j].State != S)
end
==>
ExGntd := false;
 MemData := AuxData;
end;



rule "ABS_RecvReqE11"
  CurCmd = Empty &
  forall j : NODE do 
  (Chan2[j].Cmd != Inv) & (Chan3[j].Cmd = Empty) & (Chan3[j].Cmd != InvAck)
end
==>
CurCmd := ReqE;
 CurPtr := Other;
 for j : NODE do
    InvSet[j] := ShrSet[j];
 end;
end;



rule "ABS_RecvReqS12"
  CurCmd = Empty &
  forall j : NODE do 
  (Chan2[j].Cmd != Inv) & (Chan3[j].Cmd = Empty) & (Chan3[j].Cmd != InvAck)
end
==>
CurCmd := ReqS;
 CurPtr := Other;
 for j : NODE do
    InvSet[j] := ShrSet[j];
 end;
end;




invariant "rule_1"
forall i : NODE do 
Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[i].Data = AuxData
 end ;




invariant "rule_2"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[j].Cmd != InvAck
)
 end  end ;




invariant "rule_3"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan3[j].Cmd = Empty
)
 end  end ;




invariant "rule_4"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan2[j].Cmd != Inv
)
 end  end ;




invariant "rule_5"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> ShrSet[j] = false
)
 end  end ;




invariant "rule_6"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan2[i].Cmd = Empty & ExGntd = false -> Chan2[j].Cmd != GntE
)
 end  end ;




invariant "rule_7"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan3[j].Cmd = Empty
)
 end  end ;




invariant "rule_8"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[j].State != S
)
 end  end ;




invariant "rule_9"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqE -> Chan2[j].Cmd != Inv
)
 end  end ;




invariant "rule_10"
forall i : NODE do 
Chan2[i].Cmd = Empty & ExGntd = false -> MemData = AuxData
 end ;




invariant "rule_11"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[j].Cmd != Inv
)
 end  end ;




invariant "rule_12"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (CurCmd = Empty & Chan1[i].Cmd = ReqS -> Chan3[j].Cmd != InvAck
)
 end  end ;




invariant "rule_13"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[j].Cmd != GntS
)
 end  end ;




invariant "rule_14"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[j].Cmd != InvAck
)
 end  end ;




invariant "rule_15"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> InvSet[j] = false
)
 end  end ;




invariant "rule_16"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Cache[j].State = I
)
 end  end ;




invariant "rule_17"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan2[i].Cmd = Empty & ExGntd = false -> Cache[j].State != E
)
 end  end ;




invariant "rule_18"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Chan2[j].Cmd = Empty
)
 end  end ;




invariant "rule_19"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (Chan3[i].Cmd = InvAck & ExGntd = true -> Chan3[j].Cmd = Empty
)
 end  end ;
