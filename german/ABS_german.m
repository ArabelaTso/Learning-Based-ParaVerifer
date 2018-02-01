const  ---- Configuration parameters ----

  NODE_NUM : 2;
  DATA_NUM : 2;

type   ---- Type declarations ----

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {I, S, E};
  CACHE : record State : CACHE_STATE; Data : DATA; end;

  MSG_CMD : enum {Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
  MSG : record Cmd : MSG_CMD; Data : DATA; end;

var   ---- State variables ----

  Cache : array [NODE] of CACHE;      -- Caches
  Chan1 : array [NODE] of MSG;        -- Channels for Req*
  Chan2 : array [NODE] of MSG;        -- Channels for Gnt* and Inv
  Chan3 : array [NODE] of MSG;        -- Channels for InvAck
  InvSet : array [NODE] of boolean;   -- Set of nodes to be invalidated
  ShrSet : array [NODE] of boolean;   -- Set of nodes having S or E copies
  ExGntd : boolean;                   -- E copy has been granted
  CurCmd : MSG_CMD;                   -- Current request command
  CurPtr : ABS_NODE;                  -- Current request node
  MemData : DATA;                     -- Memory data
  AuxData : DATA;                     -- Auxiliary variable for latest data

---- Initial states ----

ruleset d : DATA do startstate "Init"
  for i : NODE do
    Chan1[i].Cmd := Empty; Chan2[i].Cmd := Empty; Chan3[i].Cmd := Empty;
    Cache[i].State := I; InvSet[i] := false; ShrSet[i] := false;
  end;
  ExGntd := false; CurCmd := Empty; MemData := d; AuxData := d;
end end;

---- State transitions ----

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
rule "RecvInvAck5"
  Chan3[i].Cmd = InvAck &
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

ruleset i : NODE do
rule "RecvInvAck6"
  Chan3[i].Cmd = InvAck &
  ExGntd = false
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
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

ruleset i : NODE do
rule "SendReqE13"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqE14"
  Chan1[i].Cmd = Empty &
  Cache[i].State = S
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqS15"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;

ruleset i : NODE; data : DATA do rule "Store"
  Cache[i].State = E
==>
begin
  Cache[i].Data := data;
  AuxData := data;
endrule;endruleset;

ruleset d : DATA do
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

---- Invariant properties ----

invariant "CntrlProp"
  forall i : NODE do forall j : NODE do
    i != j -> (Cache[i].State = E -> Cache[j].State = I) &
              (Cache[i].State = S -> Cache[j].State = I | Cache[j].State = S)
  end end;

invariant "DataProp"
  ( ExGntd = false -> MemData = AuxData ) &
  forall i : NODE do Cache[i].State != I -> Cache[i].Data = AuxData end;




rule "ABS_SendGntE3"
  CurCmd = ReqE & CurPtr = Other & forall j : NODE do
    ShrSet[j] = false
  end & ExGntd = false & MemData = AuxData &
  forall j : NODE do 
  (Chan2[j].Cmd != GntE) & (Cache[j].State != E)
end
==>
ExGntd := true;
 CurCmd := Empty;
 undefine CurPtr;
end;



rule "ABS_SendGntS4"
  CurCmd = ReqS & CurPtr = Other & ExGntd = false & MemData = AuxData &
  forall j : NODE do 
  (Chan3[j].Cmd != InvAck) & (Chan2[j].Cmd != Inv) & (Chan2[j].Cmd != GntE) & (Chan3[j].Cmd = Empty) & (Cache[j].State != E)
end
==>
CurCmd := Empty;
 undefine CurPtr;
end;



rule "ABS_RecvInvAck5"
  ExGntd = true & CurCmd != Empty &
  forall j : NODE do 
  (Chan2[j].Cmd != GntS) & (ShrSet[j] = false) & (Cache[j].State != S) & (Cache[j].State = I) & (InvSet[j] = false) & (Chan2[j].Cmd = Empty) & (Chan3[j].Cmd != InvAck) & (Chan2[j].Cmd != Inv) & (Chan3[j].Cmd = Empty) & (Chan2[j].Cmd != GntE) & (Cache[j].State != E)
end
==>
ExGntd := false;
 MemData := AuxData;
end;



rule "ABS_RecvReqE11"
  CurCmd = Empty &
  forall j : NODE do 
  (Chan3[j].Cmd = Empty) & (Chan2[j].Cmd != Inv) & (Chan3[j].Cmd != InvAck)
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
  (Chan3[j].Cmd = Empty) & (Chan2[j].Cmd != Inv) & (Chan3[j].Cmd != InvAck)
end
==>
CurCmd := ReqS;
 CurPtr := Other;
 for j : NODE do
    InvSet[j] := ShrSet[j];
 end;
end;



ruleset data: DATA do rule "ABS_Store"
  ExGntd = true &
  forall j : NODE do 
  (Chan2[j].Cmd != GntS) & (ShrSet[j] = false) & (Cache[j].State != S) & (Cache[j].State = I) & (InvSet[j] = false) & (Chan2[j].Cmd = Empty) & (Chan3[j].Cmd != InvAck) & (Chan2[j].Cmd != Inv) & (Chan2[j].Cmd != GntE) & (Chan3[j].Cmd = Empty) & (Cache[j].State != E)
end
==>AuxData := data;
end;end;
