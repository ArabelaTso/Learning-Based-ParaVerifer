
const

  NODE_NUM : 2;

type

  NODE : scalarset(NODE_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : ABS_NODE;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    InvSet : array [NODE] of boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : ABS_NODE;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : ABS_NODE;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : ABS_NODE;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
  -- Program variables:
    Proc : array [NODE] of NODE_STATE;
    Dir : DIR_STATE;
    UniMsg : array [NODE] of UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  -- Auxiliary variables:
    LastWrVld : boolean;
    LastWrPtr : ABS_NODE;
    PendReqSrc : ABS_NODE;
    PendReqCmd : UNI_CMD;
    Collecting : boolean;
    FwdCmd : UNI_CMD;
    FwdSrc : ABS_NODE;
    LastInvAck : ABS_NODE;
    LastOtherInvAck : ABS_NODE;
  end;

var

  Home : NODE;
  Sta : STATE;


ruleset  src : NODE do
rule "NI_Replace1"
  Sta.RpMsg[src].Cmd = RP_Replace &
  Sta.Dir.ShrVld = true
==>
begin
  Sta.RpMsg[src].Cmd := RP_None;
  Sta.Dir.ShrSet[src] := false;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Replace2"
  Sta.RpMsg[src].Cmd = RP_Replace &
  Sta.Dir.ShrVld = false
==>
begin
  Sta.RpMsg[src].Cmd := RP_None;
endrule;
endruleset;

rule "NI_ShWb3"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = Sta.ShWbMsg.Proc |
    Sta.Dir.ShrSet[p] = true);
    Sta.Dir.ShrSet[p] := (p = Sta.ShWbMsg.Proc |
    Sta.Dir.ShrSet[p] = true);
  end;
  undefine Sta.ShWbMsg.Proc;
endrule;

rule "NI_FAck4"
  Sta.ShWbMsg.Cmd = SHWB_FAck &
  Sta.Dir.Dirty = true
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Proc;
endrule;

rule "NI_FAck5"
  Sta.ShWbMsg.Cmd = SHWB_FAck &
  Sta.Dir.Dirty = false
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  undefine Sta.ShWbMsg.Proc;
endrule;

rule "NI_Wb6"
  Sta.WbMsg.Cmd = WB_Wb
==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  undefine Sta.WbMsg.Proc;
  undefine Sta.Dir.HeadPtr;
endrule;

ruleset  src : NODE do
rule "NI_InvAck_no_exists7"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src |
    Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Dir.Dirty = false
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_no_exists8"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src |
    Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_no_exists9"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src |
    Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Dirty = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_InvAck_exists10"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  dst != src &
  Sta.Dir.InvSet[dst] = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.LastInvAck := src;
  for p : NODE do
    if ((p != src &
    Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_exists_Home11"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.LastInvAck := src;
  for p : NODE do
    if ((p != src & Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Inv12"
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv &
  Sta.Proc[dst].ProcCmd = NODE_Get
==>
begin
  Sta.InvMsg[dst].Cmd := INV_InvAck;
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.Proc[dst].InvMarked := true;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Inv13"
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv &
  Sta.Proc[dst].ProcCmd != NODE_Get
==>
begin
  Sta.InvMsg[dst].Cmd := INV_InvAck;
  Sta.Proc[dst].CacheState := CACHE_I;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Remote_PutX14"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  Sta.Proc[dst].CacheState := CACHE_E;
  undefine Sta.UniMsg[dst].Proc;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone15"
  Sta.UniMsg[Home].Cmd = UNI_PutX
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := true;
  Sta.Dir.HeadVld := false;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.Dir.HeadPtr;
endrule;

ruleset  dst : NODE do
rule "NI_Remote_Put16"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put &
  Sta.Proc[dst].InvMarked = true
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  Sta.Proc[dst].CacheState := CACHE_I;
  undefine Sta.UniMsg[dst].Proc;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Remote_Put17"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put &
  Sta.Proc[dst].InvMarked = false
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].CacheState := CACHE_S;
  undefine Sta.UniMsg[dst].Proc;
endrule;
endruleset;

rule "NI_Local_Put18"
  Sta.UniMsg[Home].Cmd = UNI_Put &
  Sta.Proc[Home].InvMarked = true
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.UniMsg[Home].Proc;
endrule;

rule "NI_Local_Put19"
  Sta.UniMsg[Home].Cmd = UNI_Put &
  Sta.Proc[Home].InvMarked = false
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].CacheState := CACHE_S;
  undefine Sta.UniMsg[Home].Proc;
endrule;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_PutX20"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src != Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := dst;
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := src;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_PutX21"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src = Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := dst;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_Nak22"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := dst;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX23"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX24"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX25"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX26"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX27"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX28"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX29"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX30"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX31"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX32"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX33"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX34"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX35"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX36"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  end;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX37"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX38"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) | (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX39"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX40"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX41"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX42"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX43"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX44"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX45"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX46"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX47"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX48"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home & p != src) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX49"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX50"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX51"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX52"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX53"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX54"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX55"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX56"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX57"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX58"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX59"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX60"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  !forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (((p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    end;
  end;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_GetX61"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_GetX62"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak63"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = true
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak64"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak65"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Put66"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src != Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := dst;
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := src;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Put67"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src = Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := dst;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Nak68"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := dst;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put69"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put70"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put71"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[src] := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = src |
    Sta.Dir.ShrSet[p] = true);
  end;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put72"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[src] := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = src |
    Sta.Dir.ShrSet[p] = true);
  end;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put73"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put74"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Get75"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_Get;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Get76"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak77"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = true
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak78"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak79"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

rule "NI_Nak_Clear80"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
begin
  Sta.NakcMsg.Cmd := NAKC_None;
  Sta.Dir.Pending := false;
endrule;

ruleset  dst : NODE do
rule "NI_Nak81"
  Sta.UniMsg[dst].Cmd = UNI_Nak
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  undefine Sta.UniMsg[dst].Proc;
endrule;
endruleset;

rule "PI_Local_Replace82"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S
==>
begin
  Sta.Dir.Local := false;
  Sta.Proc[Home].CacheState := CACHE_I;
endrule;

ruleset  src : NODE do
rule "PI_Remote_Replace83"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S
==>
begin
  Sta.Proc[src].CacheState := CACHE_I;
  Sta.RpMsg[src].Cmd := RP_Replace;
endrule;
endruleset;

rule "PI_Local_PutX84"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Pending = true
==>
begin
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Dirty := false;
endrule;

rule "PI_Local_PutX85"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Pending = false
==>
begin
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
endrule;

ruleset  dst : NODE do
rule "PI_Remote_PutX86"
  dst != Home &
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.WbMsg.Cmd := WB_Wb;
  Sta.WbMsg.Proc := dst;
endrule;
endruleset;

rule "PI_Local_GetX_PutX87"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if ((p != Home &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.Pending := true;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_PutX88"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if ((p != Home &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
    Sta.Dir.ShrSet[p] := false;
  end;
  Sta.Dir.Pending := true;
  Sta.Collecting := true;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_PutX89"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_PutX90"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_GetX91"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;

rule "PI_Local_GetX_GetX92"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;

rule "PI_Local_GetX_GetX93"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;

rule "PI_Local_GetX_GetX94"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
endrule;

ruleset  src : NODE do
rule "PI_Remote_GetX95"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_GetX;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

rule "PI_Local_Get_Put96"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Proc[Home].InvMarked = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_I;
endrule;

rule "PI_Local_Get_Put97"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Proc[Home].InvMarked = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].CacheState := CACHE_S;
endrule;

rule "PI_Local_Get_Get98"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_Get;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_Get;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;

rule "PI_Local_Get_Get99"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_Get;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;

ruleset  src : NODE do
rule "PI_Remote_Get100"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_Get;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Home;
endrule;
endruleset;

ruleset  src : NODE do
rule "Store101"
  Sta.Proc[src].CacheState = CACHE_E
==>
begin
  Sta.LastWrVld := true;
  Sta.LastWrPtr := src;
endrule;
endruleset;

ruleset  h : NODE do
startstate
  Home := h;
  undefine Sta;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  end;
  Sta.LastWrVld := false;
  Sta.Collecting := false;
  Sta.FwdCmd := UNI_None;
endstartstate;
endruleset;
invariant "CacheStateProp"
  forall p : NODE do
    forall q : NODE do
      (p != q ->
      !(Sta.Proc[p].CacheState = CACHE_E &
      Sta.Proc[q].CacheState = CACHE_E))
    end
  end;


rule "ABS_NI_InvAck_no_exists7_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Collecting = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & Sta.Dir.Local = true
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & forall p : NODE do
    False |
    Sta.Dir.InvSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := false;
 Sta.Dir.Local := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_no_exists8_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = true
 & Sta.PendReqSrc != Other
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & forall p : NODE do
    False |
    Sta.Dir.InvSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_no_exists9_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = true
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & forall p : NODE do
    False |
    Sta.Dir.InvSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_exists_Home11_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = true
 & Sta.Dir.InvSet[Home] = true
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.LastInvAck := Other;
 for p : NODE do
    if ((True & Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
end;

rule "ABS_NI_Local_GetX_PutX23_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Local := false;
 Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
end;

rule "ABS_NI_Local_GetX_PutX24_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Local := false;
 Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
end;

rule "ABS_NI_Local_GetX_PutX25_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX26_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX27_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX28_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX29_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX30_i"
  Sta.Dir.Dirty = false
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX31_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX32_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX33_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX34_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX35_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX36_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := true;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Dir.ShrVld := false;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 Sta.Dir.InvSet[p] := false;
 end;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX37_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX38_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) | (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX39_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX40_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX41_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX42_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX43_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX44_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True & Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX45_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX46_i"
  Sta.Dir.HeadVld = true
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_GetX
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Other
 & Sta.Proc[Home].CacheState = CACHE_S
 & True
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX47_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX48_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home & True) & ((Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true) |  (Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX49_i"
  Sta.Dir.HeadVld = true
 & Sta.Dir.Dirty = false
 & Sta.Dir.HeadPtr = Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Other
 & Sta.Proc[Home].CacheState = CACHE_S
 & True
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX50_i"
  Sta.Dir.HeadVld = true
 & Sta.Dir.Dirty = false
 & Sta.Dir.HeadPtr = Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & True
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX51_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX52_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Proc[Home].CacheState := CACHE_I;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX53_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX54_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX55_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX56_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX57_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX58_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX59_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX60_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Pending := true;
 Sta.Dir.Dirty := true;
 for p : NODE do
    if (((p != Home &
    True) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
 Sta.InvMsg[p].Cmd := INV_Inv;
 else
      Sta.Dir.InvSet[p] := false;
 Sta.InvMsg[p].Cmd := INV_None;
 end;
 end;
 Sta.Dir.ShrVld := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 for p : NODE do
    if ((True &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_GetX61_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := true;
 Sta.FwdCmd := UNI_GetX;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_GetX_GetX62_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.Dir.HeadPtr = Home
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := true;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_Get_Put69_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Proc[Home].CacheState := CACHE_S;
end;

rule "ABS_NI_Local_Get_Put70_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.Dirty := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.Proc[Home].CacheState := CACHE_S;
end;

rule "ABS_NI_Local_Get_Put71_i"
  Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Pending = false
 & Sta.FwdCmd != UNI_Get
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other &
  forall j : NODE do 
  (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.ShrVld := true;
 for p : NODE do
    Sta.Dir.InvSet[p] := (False |
    Sta.Dir.ShrSet[p] = true);
 end;
end;

rule "ABS_NI_Local_Get_Put72_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.ShrVld := true;
 for p : NODE do
    Sta.Dir.InvSet[p] := (False |
    Sta.Dir.ShrSet[p] = true);
 end;
end;

rule "ABS_NI_Local_Get_Put73_i"
  Sta.Dir.Dirty = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_Get_Put74_i"
  Sta.Dir.Dirty = false
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = true
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState = CACHE_I)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_Get_Get75_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := true;
 Sta.FwdCmd := UNI_Get;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_Get;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_Get_Get76_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Pending = false
 & Sta.Dir.HeadPtr = Home
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.ShWbMsg.Proc != j)
end
==>
Sta.Dir.Pending := true;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_Get;
 Sta.Collecting := false;
end;

rule "ABS_PI_Remote_PutX86_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.WbMsg.Cmd := WB_Wb;
 Sta.WbMsg.Proc := Other;
end;

rule "ABS_Store101_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.LastWrVld := true;
 Sta.LastWrPtr := Other;
end;


ruleset j : NODE do rule "ABS_NI_InvAck_exists10_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = true
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.InvSet[j] = true)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.LastInvAck := Other;
 for p : NODE do
    if ((True &
    Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
end;end;


ruleset i : NODE do rule "ABS_NI_InvAck_exists10_j"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = true
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other &
  
  (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.InvMsg[i].Cmd = INV_InvAck)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Dir.InvSet[i] = true)
 & (Sta.Dir.HeadPtr != i)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.InvMsg[i].Cmd := INV_None;
 Sta.LastInvAck := i;
 for p : NODE do
    if ((p != i &
    Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
 Sta.Dir.InvSet[i] := false;
end;end;

rule "ABS_NI_InvAck_exists10"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.FwdCmd != UNI_GetX
 & Sta.Collecting = true
 & Sta.Dir.HeadPtr != Other
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.Pending = true
 & Sta.ShWbMsg.Proc != Other
 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.LastInvAck := Other;
 for p : NODE do
    if ((True &
    Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
end;


ruleset j : NODE do rule "ABS_NI_Remote_GetX_PutX20_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (j != Home)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_I;
 Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_PutX20_j"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.ShWbMsg.Proc != i)
 & (i != Home)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_PutX;
 Sta.UniMsg[i].Proc := Other;
 Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := i;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_GetX_PutX20"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & forall p : NODE do
   Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_GetX_PutX21_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & False
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (j != Home)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_I;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_PutX21_j"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (i = Home)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_PutX;
 Sta.UniMsg[i].Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_GetX_PutX21"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & False
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & forall p : NODE do
   Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_GetX_Nak22_i"
  True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  
  (j != Home)
 & (Sta.Proc[j].CacheState != CACHE_E)

==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_Nak22_j"
  True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)

==>
Sta.UniMsg[i].Cmd := UNI_Nak;
 Sta.UniMsg[i].Proc := Other;
 Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_GetX_Nak22"
  Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Proc[Home].InvMarked = false
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Put66_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (j != Home)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_S;
 Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Put66_j"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.ShWbMsg.Proc != i)
 & (i != Home)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_Put;
 Sta.UniMsg[i].Proc := Other;
 Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := i;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_Get_Put66"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & forall p : NODE do
   Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Put67_i"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.ShWbMsg.Proc != Other
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & False
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (j != Home)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_S;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Put67_j"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Local = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.ShWbMsg.Proc != Home
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.Proc[Home].CacheState = CACHE_I &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (i = Home)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)

 & forall p : NODE do
   Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_Put;
 Sta.UniMsg[i].Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_Get_Put67"
  Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Dirty = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.ShWbMsg.Proc != Home
 & Sta.Dir.Local = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState != CACHE_E
 & False
 & True
 & Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & forall p : NODE do
   Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Nak68_i"
  True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  
  (j != Home)
 & (Sta.Proc[j].CacheState != CACHE_E)

==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Nak68_j"
  True
 & Sta.Dir.InvSet[Home] = false
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_S)

==>
Sta.UniMsg[i].Cmd := UNI_Nak;
 Sta.UniMsg[i].Proc := Other;
 Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_Get_Nak68"
  Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Proc[Home].InvMarked = false
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;
