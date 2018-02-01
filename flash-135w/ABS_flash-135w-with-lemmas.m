
const

  NODE_NUM : 3;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
    CacheData : DATA;
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
    Data : DATA;
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
    Data : DATA;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
  -- Program variables:
    Proc : array [NODE] of NODE_STATE;
    Dir : DIR_STATE;
    MemData : DATA;
    UniMsg : array [NODE] of UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  -- Auxiliary variables:
    CurrData : DATA;
    PrevData : DATA;
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
  Sta.MemData := Sta.ShWbMsg.Data;
  undefine Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Data;
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
  undefine Sta.ShWbMsg.Data;
endrule;

rule "NI_FAck5"
  Sta.ShWbMsg.Cmd = SHWB_FAck &
  Sta.Dir.Dirty = false
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  undefine Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Data;
endrule;

rule "NI_Wb6"
  Sta.WbMsg.Cmd = WB_Wb
==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.MemData := Sta.WbMsg.Data;
  undefine Sta.WbMsg.Proc;
  undefine Sta.WbMsg.Data;
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
    p = src | Sta.Dir.InvSet[p] = false
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
    if ((p != src &
    Sta.Dir.InvSet[p] = true)) then
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
  undefine Sta.Proc[dst].CacheData;
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
  undefine Sta.Proc[dst].CacheData;
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
  Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
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
  Sta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.Proc[dst].CacheData;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
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
  Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
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
  Sta.MemData := Sta.UniMsg[Home].Data;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
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
  Sta.MemData := Sta.UniMsg[Home].Data;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
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
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := src;
  undefine Sta.ShWbMsg.Data;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.Proc[dst].CacheData;
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
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.Proc[dst].CacheData;
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
  undefine Sta.UniMsg[src].Data;
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
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX25"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := src;
  Sta.ShWbMsg.Data := Sta.Proc[dst].CacheData;
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
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
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
  undefine Sta.UniMsg[src].Data;
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
  Sta.MemData := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
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
  Sta.MemData := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
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
  Sta.UniMsg[src].Data := Sta.MemData;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.UniMsg[dst].Data;
endrule;
endruleset;

rule "PI_Local_Replace82"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S
==>
begin
  Sta.Dir.Local := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
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
  undefine Sta.Proc[src].CacheData;
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
  Sta.MemData := Sta.Proc[Home].CacheData;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.MemData := Sta.Proc[Home].CacheData;
  undefine Sta.Proc[Home].CacheData;
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
  Sta.WbMsg.Data := Sta.Proc[dst].CacheData;
  undefine Sta.Proc[dst].CacheData;
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
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
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
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
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
  Sta.Proc[Home].CacheData := Sta.MemData;
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
  Sta.Proc[Home].CacheData := Sta.MemData;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[src].Data;
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
  undefine Sta.Proc[Home].CacheData;
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
  Sta.Proc[Home].CacheData := Sta.MemData;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[Home].Data;
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
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;


ruleset  src : NODE; data : DATA  do
rule "Store101"
  Sta.Proc[src].CacheState = CACHE_E
==>
begin
  Sta.Proc[src].CacheData := data;
  Sta.CurrData := data;
  Sta.LastWrVld := true;
  Sta.LastWrPtr := src;
endrule;
endruleset;

ruleset  h : NODE; d : DATA do
startstate
  Home := h;
  undefine Sta;
  Sta.MemData := d;
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
  Sta.CurrData := d;
  Sta.PrevData := d;
  Sta.LastWrVld := false;
  Sta.Collecting := false;
  Sta.FwdCmd := UNI_None;
endstartstate;
endruleset;

invariant "CacheStateProp"
  forall p : NODE do forall q : NODE do
    p != q ->
    !(Sta.Proc[p].CacheState = CACHE_E & Sta.Proc[q].CacheState = CACHE_E)
  end end;

invariant "CacheDataProp"
  forall p : NODE do
    ( Sta.Proc[p].CacheState = CACHE_E ->
      Sta.Proc[p].CacheData = Sta.CurrData ) &
    ( Sta.Proc[p].CacheState = CACHE_S ->
      ( Sta.Collecting -> Sta.Proc[p].CacheData = Sta.PrevData ) &
      (!Sta.Collecting -> Sta.Proc[p].CacheData = Sta.CurrData ) )
  end;

invariant "MemDataProp"
  !Sta.Dir.Dirty -> Sta.MemData = Sta.CurrData;


ruleset data: DATA do rule "ABS_Store101_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>Sta.CurrData := data;
 Sta.LastWrVld := true;
 Sta.LastWrPtr := Other;
end;end;

rule "ABS_NI_InvAck_no_exists7_i"
  Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.InvSet[Home] = false
 & forall p : NODE do
    False |
    Sta.Dir.InvSet[p] = false
  end
 & Sta.Dir.ShrVld = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.HeadPtr != j)
end
==>
Sta.Dir.Pending := false;
 Sta.Dir.Local := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_no_exists8_i"
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.PendReqSrc != Other
 & Sta.Dir.Local = false
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & forall p : NODE do
    False | Sta.Dir.InvSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
end
==>
Sta.Dir.Pending := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_no_exists9_i"
  Sta.Dir.InvSet[Home] = false
 & forall p : NODE do
    False |
    Sta.Dir.InvSet[p] = false
  end
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].InvMarked = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.PrevData
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
end
==>
Sta.Dir.Pending := false;
 Sta.Collecting := false;
 Sta.LastInvAck := Other;
end;

rule "ABS_NI_InvAck_exists_Home11_i"
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.InvSet[Home] = true
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
end
==>
Sta.LastInvAck := Other;
 for p : NODE do
    if ((True &
    Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
 end;
 end;
end;

rule "ABS_NI_Local_GetX_PutX23_i"
  Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
end;

rule "ABS_NI_Local_GetX_PutX24_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
end;

rule "ABS_NI_Local_GetX_PutX25_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX26_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX27_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX28_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX29_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX30_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX31_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX32_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_I;
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX33_i"
  Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX34_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX35_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX36_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
end;

rule "ABS_NI_Local_GetX_PutX37_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX38_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX39_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX40_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX41_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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

rule "ABS_NI_Local_GetX_PutX42_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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

rule "ABS_NI_Local_GetX_PutX43_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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

rule "ABS_NI_Local_GetX_PutX44_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Proc[Home].ProcCmd = NODE_Get
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Proc[Home].InvMarked := true;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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

rule "ABS_NI_Local_GetX_PutX45_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX46_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Proc[Home].InvMarked = false
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & True
 & Sta.Dir.Pending = false
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX47_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX48_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX49_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.Dir.InvSet[Home] = false
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Pending = false
 & True
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_Get
 & Sta.FwdCmd != UNI_GetX
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Pending = false
 & True
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Collecting = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.HeadPtr = Other
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 undefine Sta.Proc[Home].CacheData;
 Sta.Dir.Local := false;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := true;
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX54_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX55_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX56_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 Sta.PrevData := Sta.CurrData;
 Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
 for p : NODE do
    Sta.Dir.ShrSet[p] := false;
 end;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_GetX_PutX57_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
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
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.HeadPtr = Other
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & !forall p : NODE do
    True ->
    Sta.Dir.ShrSet[p] = false
  end
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & Sta.Dir.Pending = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 Sta.PrevData := Sta.CurrData;
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
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Dir.Pending = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.Pending := true;
 Sta.FwdCmd := UNI_GetX;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_GetX_GetX62_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.HeadPtr = Home
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.Pending := true;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_GetX;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_Get_Put69_i"
  Sta.Dir.Dirty = false
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.Dirty := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.MemData := Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_S;
end;

rule "ABS_NI_Local_Get_Put70_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
end
==>
Sta.Dir.Dirty := false;
 Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
 Sta.MemData := Sta.Proc[Home].CacheData;
 Sta.Proc[Home].CacheState := CACHE_S;
end;

rule "ABS_NI_Local_Get_Put71_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.Dirty = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].InvMarked = false
 & True
 & Sta.Dir.Pending = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.ShrVld := true;
 for p : NODE do
    Sta.Dir.InvSet[p] := (False |
    Sta.Dir.ShrSet[p] = true);
 end;
end;

rule "ABS_NI_Local_Get_Put72_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].CacheState = CACHE_S
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
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
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
end
==>
Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_Get_Put74_i"
  Sta.Proc[Home].CacheState != CACHE_I
 & Sta.Dir.Dirty = false
 & Sta.Dir.Local = true
 & Sta.FwdCmd != UNI_Get
 & Sta.Dir.HeadVld = false
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheData = Sta.CurrData
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].CacheState = CACHE_E
 & True
 & Sta.Dir.Pending = false
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].ProcCmd = NODE_None
 & Sta.FwdCmd = UNI_None
 & Sta.MemData = Sta.CurrData
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].ProcCmd != NODE_Get
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_I)
end
==>
Sta.Dir.HeadVld := true;
 Sta.Dir.HeadPtr := Other;
end;

rule "ABS_NI_Local_Get_Get75_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Dir.Pending = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.Pending := true;
 Sta.FwdCmd := UNI_Get;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_Get;
 Sta.Collecting := false;
end;

rule "ABS_NI_Local_Get_Get76_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true
 & Sta.Collecting = false
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Pending = false
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.Dir.HeadPtr = Home
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Proc[Home].InvMarked = false &
  forall j : NODE do 
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
end
==>
Sta.Dir.Pending := true;
 Sta.PendReqSrc := Other;
 Sta.PendReqCmd := UNI_Get;
 Sta.Collecting := false;
end;

rule "ABS_PI_Remote_PutX86_i"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].InvMarked = false
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.Dir.HeadVld = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Dir.Dirty = true &
  forall j : NODE do 
  (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
end
==>
Sta.WbMsg.Cmd := WB_Wb;
 Sta.WbMsg.Proc := Other;
 Sta.WbMsg.Data := Sta.CurrData;
end;


ruleset j : NODE do rule "ABS_NI_InvAck_exists10_i"
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.InvSet[j] = true)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Dir.ShrSet[j] = false)
 & (Sta.Dir.HeadPtr != j)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.ShWbMsg.Proc != p end
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
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.Dir.InvSet[i] = true)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.Proc[i].CacheState != CACHE_S)
 & (Sta.InvMsg[i].Cmd = INV_InvAck)
 & (Sta.Dir.HeadPtr != i)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.ShWbMsg.Proc != p end
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
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd != UNI_Get
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.Collecting = true
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.FwdCmd = UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false
 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.ShWbMsg.Proc != p end
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
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].CacheData = Sta.CurrData)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_I;
 Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := Other;
 undefine Sta.ShWbMsg.Data;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
 undefine Sta.Proc[j].CacheData;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_PutX20_j"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.PendReqSrc != Other
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (i != Home)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_PutX;
 Sta.UniMsg[i].Proc := Other;
 Sta.UniMsg[i].Data := Sta.CurrData;
 Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := i;
 undefine Sta.ShWbMsg.Data;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_GetX_PutX20"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & True
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.PendReqSrc != Other
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true
 & forall p : NODE do
   Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.ShWbMsg.Cmd := SHWB_FAck;
 Sta.ShWbMsg.Proc := Other;
 undefine Sta.ShWbMsg.Data;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_GetX_PutX21_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & False
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].CacheData = Sta.CurrData)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_I;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
 undefine Sta.Proc[j].CacheData;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_PutX21_j"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.PendReqSrc != Other
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)
 & (i = Home)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_PutX;
 Sta.UniMsg[i].Proc := Other;
 Sta.UniMsg[i].Data := Sta.CurrData;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_GetX_PutX21"
  Sta.Dir.HeadPtr != Home
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & True
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.PendReqSrc != Other
 & Sta.WbMsg.Cmd != WB_Wb
 & False
 & Sta.Dir.Local = false
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true
 & forall p : NODE do
   Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_GetX_Nak22_i"
  Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_GetX_Nak22_j"
  Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.PendReqSrc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.Proc[i].InvMarked = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].ProcCmd = NODE_GetX)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_Get)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.UniMsg[i].Cmd = UNI_GetX)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.UniMsg[i].Cmd := UNI_Nak;
 Sta.UniMsg[i].Proc := Other;
 Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
 undefine Sta.UniMsg[i].Data;
end;end;

rule "ABS_NI_Remote_GetX_Nak22"
  Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.FwdCmd = UNI_GetX
 & Sta.FwdCmd != UNI_Get
 & Sta.Proc[Home].InvMarked = false
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.PendReqSrc != Other
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Put66_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].CacheData = Sta.CurrData)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_S;
 Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := Other;
 Sta.ShWbMsg.Data := Sta.Proc[j].CacheData;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Put66_j"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.PendReqSrc != Other
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.RpMsg[i].Cmd != RP_Replace)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (i != Home)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_Put;
 Sta.UniMsg[i].Proc := Other;
 Sta.UniMsg[i].Data := Sta.CurrData;
 Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := i;
 Sta.ShWbMsg.Data := Sta.CurrData;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_Get_Put66"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.PendReqSrc != Other
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true
 & forall p : NODE do
   Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.ShWbMsg.Cmd := SHWB_ShWb;
 Sta.ShWbMsg.Proc := Other;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Put67_i"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & False
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Get)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.UniMsg[j].Cmd != UNI_GetX)
 & (Sta.UniMsg[j].Proc != Other)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.UniMsg[j].Cmd != UNI_Nak)
 & (Sta.Proc[j].ProcCmd != NODE_Get)
 & (Sta.UniMsg[j].Cmd != UNI_PutX)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].ProcCmd != NODE_GetX)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].ProcCmd = NODE_None)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.UniMsg[j].Proc != Home)
 & (Sta.Proc[j].CacheData = Sta.CurrData)
 & (Sta.InvMsg[j].Cmd != INV_Inv)
 & (Sta.Proc[j].CacheState = CACHE_E)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.Proc[j].CacheState := CACHE_S;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Put67_j"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.PendReqSrc != Other
 & Sta.ShWbMsg.Proc != Home
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadVld = true
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.WbMsg.Cmd != WB_Wb
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (i = Home)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.RpMsg[i].Cmd != RP_Replace)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.UniMsg[i].Cmd != UNI_PutX)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false
 & Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX end
==>
Sta.UniMsg[i].Cmd := UNI_Put;
 Sta.UniMsg[i].Proc := Other;
 Sta.UniMsg[i].Data := Sta.CurrData;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
end;end;

rule "ABS_NI_Remote_Get_Put67"
  Sta.Dir.HeadPtr != Home
 & Sta.FwdCmd = UNI_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.FwdCmd != UNI_None
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.ShWbMsg.Proc != Home
 & Sta.PendReqSrc != Other
 & Sta.WbMsg.Cmd != WB_Wb
 & False
 & Sta.Dir.Local = false
 & Sta.Collecting = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.Dirty = true
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Proc[Home].InvMarked = false
 & Sta.Dir.HeadVld = true
 & forall p : NODE do
   Sta.Proc[p].CacheState != CACHE_E
 & Sta.ShWbMsg.Proc != p
 & Sta.UniMsg[p].Cmd != UNI_PutX
 & Sta.Dir.ShrSet[p] = false end
==>
Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;


ruleset j : NODE do rule "ABS_NI_Remote_Get_Nak68_i"
  Sta.FwdCmd = UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.Dir.ShrSet[j] = false)
 & (Sta.UniMsg[j].Cmd != UNI_Put)
 & (Sta.Proc[j].CacheState != CACHE_E)
 & (Sta.InvMsg[j].Cmd != INV_InvAck)
 & (Sta.ShWbMsg.Proc != j)
 & (Sta.Proc[j].CacheState != CACHE_S)
 & (Sta.Dir.InvSet[j] = false)
 & (Sta.PendReqSrc != j)
 & (j != Home)
 & (Sta.Proc[j].InvMarked = false)
 & (Sta.InvMsg[j].Cmd != INV_Inv)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;end;


ruleset i : NODE do rule "ABS_NI_Remote_Get_Nak68_j"
  Sta.FwdCmd = UNI_Get
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.PendReqSrc != Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & True
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.Proc[Home].InvMarked = false &
  
  (Sta.PendReqSrc = i)
 & (Sta.Dir.InvSet[i] = false)
 & (Sta.UniMsg[i].Proc = Other)
 & (Sta.Proc[i].CacheState != CACHE_E)
 & (Sta.RpMsg[i].Cmd != RP_Replace)
 & (Sta.Proc[i].ProcCmd = NODE_Get)
 & (Sta.InvMsg[i].Cmd != INV_Inv)
 & (Sta.Dir.HeadPtr != i)
 & (Sta.Proc[i].ProcCmd != NODE_None)
 & (Sta.UniMsg[i].Cmd = UNI_Get)
 & (Sta.ShWbMsg.Proc != i)
 & (Sta.InvMsg[i].Cmd != INV_InvAck)
 & (Sta.Proc[i].ProcCmd != NODE_GetX)
 & (Sta.Proc[i].CacheState = CACHE_I)
 & (Sta.Dir.ShrSet[i] = false)
 & (Sta.Proc[i].CacheState != CACHE_S)

 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.UniMsg[i].Cmd := UNI_Nak;
 Sta.UniMsg[i].Proc := Other;
 Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := i;
 undefine Sta.UniMsg[i].Data;
end;end;

rule "ABS_NI_Remote_Get_Nak68"
  Sta.FwdCmd = UNI_Get
 & Sta.Dir.InvSet[Home] = false
 & Sta.Dir.ShrVld = false
 & Sta.Proc[Home].InvMarked = false
 & True
 & Sta.ShWbMsg.Cmd != SHWB_ShWb
 & Sta.FwdCmd != UNI_None
 & Sta.PendReqSrc != Other
 & Sta.Dir.Local = false
 & Sta.UniMsg[Home].Cmd != UNI_Put
 & Sta.PendReqSrc = Other
 & Sta.Proc[Home].CacheState = CACHE_I
 & Sta.Proc[Home].CacheState != CACHE_E
 & Sta.ShWbMsg.Cmd != SHWB_FAck
 & Sta.Dir.HeadPtr != Other
 & Sta.FwdCmd != UNI_GetX
 & Sta.ShWbMsg.Proc != Other
 & Sta.Proc[Home].CacheState != CACHE_S
 & Sta.Dir.Pending = true
 & Sta.UniMsg[Home].Cmd != UNI_PutX
 & Sta.Collecting = false
 & forall p : NODE do
   Sta.Dir.ShrSet[p] = false end
==>
Sta.NakcMsg.Cmd := NAKC_Nakc;
 Sta.FwdCmd := UNI_None;
 Sta.FwdSrc := Other;
end;




invariant "rule_1"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState = CACHE_I
)
end end ;




invariant "rule_2"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.InvMsg[j].Cmd != INV_Inv
)
end ;




invariant "rule_3"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrVld = false
)
end ;




invariant "rule_4"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Proc[j].CacheState != CACHE_S
)
end end ;




invariant "rule_5"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.InvSet[i] = false
)
end end ;




invariant "rule_6"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState != CACHE_S
)
end ;




invariant "rule_7"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheData = Sta.CurrData
;




invariant "rule_8"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrVld = false
)
end end ;




invariant "rule_9"

Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Dirty = false
;




invariant "rule_10"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState = CACHE_I
)
end ;




invariant "rule_11"

Sta.Dir.Dirty = false -> Sta.Proc[Home].CacheState != CACHE_E
;




invariant "rule_12"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.Pending = true
)
end end ;




invariant "rule_13"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i
)
end ;




invariant "rule_14"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd != UNI_None
)
end end ;




invariant "rule_15"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end end ;




invariant "rule_16"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end ;




invariant "rule_17"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_GetX
)
end ;




invariant "rule_18"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = false -> Sta.Proc[Home].CacheState = CACHE_I
)
end ;




invariant "rule_19"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Local = false
;




invariant "rule_20"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HeadVld = true
)
end ;




invariant "rule_21"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_22"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[i].Cmd != UNI_PutX
)
end ;




invariant "rule_23"

Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_24"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end end ;




invariant "rule_25"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_None
)
end ;




invariant "rule_26"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end ;




invariant "rule_27"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_None
)
end ;




invariant "rule_28"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.FwdCmd = UNI_None
;




invariant "rule_29"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[j].Cmd != INV_Inv
)
end end ;




invariant "rule_30"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_E
)
end ;




invariant "rule_31"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[i] = false
)
end ;




invariant "rule_32"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState != CACHE_E -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_33"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.Local = false
)
end end ;




invariant "rule_34"

Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Collecting = true
;




invariant "rule_35"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Proc[j].CacheState != CACHE_S
)
end end ;




invariant "rule_36"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false
)
end end ;




invariant "rule_37"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_38"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[Home].CacheState = CACHE_I
)
end ;




invariant "rule_39"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.Dir.Pending = false
;




invariant "rule_40"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end ;




invariant "rule_41"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_I
)
end ;




invariant "rule_42"

Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_43"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd != UNI_None
)
end end ;




invariant "rule_44"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Proc != Home
)
end ;




invariant "rule_45"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState = CACHE_I
)
end ;




invariant "rule_46"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E
)
end end ;




invariant "rule_47"

Sta.Dir.HeadVld = true -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_48"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX
)
end end ;




invariant "rule_49"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end end ;




invariant "rule_50"

Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState != CACHE_E
;




invariant "rule_51"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_GetX
)
end ;




invariant "rule_52"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_53"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Proc[i].CacheState != CACHE_S
)
end end ;




invariant "rule_54"

Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E
;




invariant "rule_55"

Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_56"

Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb
;




invariant "rule_57"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Get
)
end ;




invariant "rule_58"

Sta.Dir.Pending = false -> Sta.FwdCmd = UNI_None
;




invariant "rule_59"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.Collecting = false
;




invariant "rule_60"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end ;




invariant "rule_61"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end ;




invariant "rule_62"

Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_GetX
;




invariant "rule_63"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.FwdCmd = UNI_None
)
end ;




invariant "rule_64"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_65"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Nak
)
end ;




invariant "rule_66"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_67"

Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != Home
;




invariant "rule_68"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState = CACHE_I
)
end ;




invariant "rule_69"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false
)
end ;




invariant "rule_70"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.Dirty = false -> Sta.Dir.HeadPtr != j
)
end ;




invariant "rule_71"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end ;




invariant "rule_72"

Sta.Dir.Dirty = false -> Sta.WbMsg.Cmd != WB_Wb
;




invariant "rule_73"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb
)
end ;




invariant "rule_74"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end end ;




invariant "rule_75"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_76"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[i].Cmd != INV_InvAck
)
end end ;




invariant "rule_77"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[j] = false
)
end ;




invariant "rule_78"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end ;




invariant "rule_79"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.FwdCmd != UNI_Get
;




invariant "rule_80"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_81"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState != CACHE_E
)
end end ;




invariant "rule_82"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false
)
end ;




invariant "rule_83"

Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_Get
;




invariant "rule_84"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.PendReqSrc != j
)
end end ;




invariant "rule_85"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Proc[i].CacheState = CACHE_I
)
end end ;




invariant "rule_86"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Dir.Pending = false
;




invariant "rule_87"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.HeadPtr != j -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_88"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.Pending = true
)
end ;




invariant "rule_89"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None
)
end ;




invariant "rule_90"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Collecting = true
)
end ;




invariant "rule_91"

Sta.Dir.HeadPtr != Home -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_92"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd = UNI_GetX
)
end end ;




invariant "rule_93"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState != CACHE_S
)
end end ;




invariant "rule_94"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end ;




invariant "rule_95"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Proc != i
)
end end ;




invariant "rule_96"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.InvSet[i] = false
)
end end ;




invariant "rule_97"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end ;




invariant "rule_98"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState = CACHE_I
)
end ;




invariant "rule_99"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[j].Cmd != UNI_Put
)
end end ;




invariant "rule_100"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E
)
end end ;




invariant "rule_101"

Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Dir.Dirty = false
;




invariant "rule_102"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_103"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Nak
)
end ;




invariant "rule_104"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].InvMarked = false
)
end ;




invariant "rule_105"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get
)
end ;




invariant "rule_106"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_107"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Dir.Pending = false
)
end ;




invariant "rule_108"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState != CACHE_E
)
end end ;




invariant "rule_109"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_Get
)
end ;




invariant "rule_110"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd != UNI_Get
)
end end ;




invariant "rule_111"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.Local = false
)
end end ;




invariant "rule_112"

Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_113"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Collecting = false
;




invariant "rule_114"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_115"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end ;




invariant "rule_116"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end end ;




invariant "rule_117"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end end ;




invariant "rule_118"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadVld = true
)
end ;




invariant "rule_119"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_120"

Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I
;




invariant "rule_121"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Proc[i].ProcCmd != NODE_None
)
end end ;




invariant "rule_122"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Dir.Dirty = false
;




invariant "rule_123"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX
;




invariant "rule_124"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.Pending = true
)
end ;




invariant "rule_125"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end ;




invariant "rule_126"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j
)
end ;




invariant "rule_127"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E
;




invariant "rule_128"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end ;




invariant "rule_129"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[j].Cmd != INV_Inv
)
end end ;




invariant "rule_130"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].InvMarked = false
)
end end ;




invariant "rule_131"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrSet[j] = false
)
end end ;




invariant "rule_132"

Sta.Dir.Local = true & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheData = Sta.CurrData
;




invariant "rule_133"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd != NODE_GetX
)
end ;




invariant "rule_134"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX
)
end ;




invariant "rule_135"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_136"

Sta.Dir.HeadPtr != Home -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_137"

Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_PutX
;




invariant "rule_138"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end end ;




invariant "rule_139"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_S
)
end ;




invariant "rule_140"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end end ;




invariant "rule_141"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[j].CacheState != CACHE_S
)
end ;




invariant "rule_142"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false
)
end ;




invariant "rule_143"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E
)
end ;




invariant "rule_144"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheData = Sta.CurrData
)
end ;




invariant "rule_145"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.Dirty = true
)
end ;




invariant "rule_146"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.Local = false
)
end ;




invariant "rule_147"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i
)
end ;




invariant "rule_148"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != Home
)
end ;




invariant "rule_149"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.InvMsg[j].Cmd != INV_Inv
)
end end ;




invariant "rule_150"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false
)
end ;




invariant "rule_151"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E
)
end ;




invariant "rule_152"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end ;




invariant "rule_153"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState = CACHE_S
)
end ;




invariant "rule_154"

Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Dir.HeadVld = false
;




invariant "rule_155"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrVld = false
)
end ;




invariant "rule_156"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != j
)
end ;




invariant "rule_157"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Dir.InvSet[Home] = false
)
end end ;




invariant "rule_158"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_Get
)
end ;




invariant "rule_159"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[j] = false
)
end ;




invariant "rule_160"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrVld = false
)
end end ;




invariant "rule_161"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_162"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Put
)
end ;




invariant "rule_163"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.PendReqSrc = i
)
end end ;




invariant "rule_164"

Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb
;




invariant "rule_165"

Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != Home
;




invariant "rule_166"

Sta.Dir.Local = true & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_I
;




invariant "rule_167"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.UniMsg[j].Cmd != UNI_Put
)
end end ;




invariant "rule_168"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].CacheData = Sta.CurrData
)
end ;




invariant "rule_169"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_S
)
end ;




invariant "rule_170"

Sta.Dir.Pending = false -> Sta.Collecting = false
;




invariant "rule_171"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != j
)
end ;




invariant "rule_172"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadPtr != j -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end ;




invariant "rule_173"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.UniMsg[j].Cmd != UNI_Get
)
end ;




invariant "rule_174"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get
)
end ;




invariant "rule_175"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false
)
end ;




invariant "rule_176"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None
)
end ;




invariant "rule_177"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Dir.Dirty = false
)
end ;




invariant "rule_178"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Proc != Home
)
end ;




invariant "rule_179"

Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S
;




invariant "rule_180"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_181"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.FwdCmd != UNI_GetX
;




invariant "rule_182"

Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false
;




invariant "rule_183"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end end ;




invariant "rule_184"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.HeadPtr != i
)
end end ;




invariant "rule_185"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrSet[i] = false
)
end end ;




invariant "rule_186"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState != CACHE_E -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_187"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get
)
end ;




invariant "rule_188"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.MemData = Sta.PrevData
)
end ;




invariant "rule_189"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Collecting = false
)
end end ;




invariant "rule_190"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Collecting = true
)
end ;




invariant "rule_191"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_S
)
end ;




invariant "rule_192"

Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_193"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheData = Sta.CurrData
)
end ;




invariant "rule_194"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != i
)
end ;




invariant "rule_195"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_Inv
)
end ;




invariant "rule_196"

Sta.Dir.Pending = true -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_197"

Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_198"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Dirty = true
)
end ;




invariant "rule_199"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_S
)
end ;




invariant "rule_200"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false
)
end end ;




invariant "rule_201"

Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_202"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end end ;




invariant "rule_203"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j
)
end ;




invariant "rule_204"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S
;




invariant "rule_205"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[i].Cmd != INV_Inv
)
end end ;




invariant "rule_206"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_207"

Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.MemData = Sta.CurrData
;




invariant "rule_208"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != Home
)
end ;




invariant "rule_209"

Sta.Dir.Pending = true & Sta.Dir.Dirty = false -> Sta.Dir.HeadVld = false
;




invariant "rule_210"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_E
)
end ;




invariant "rule_211"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrSet[j] = false
)
end end ;




invariant "rule_212"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.InvSet[j] = false
)
end end ;




invariant "rule_213"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E
)
end ;




invariant "rule_214"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_215"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.ShrSet[i] = false
)
end end ;




invariant "rule_216"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.HeadPtr != j -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_217"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb
)
end ;




invariant "rule_218"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.RpMsg[i].Cmd != RP_Replace
)
end end ;




invariant "rule_219"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.Pending = true
)
end end ;




invariant "rule_220"

Sta.Dir.Dirty = false -> Sta.MemData = Sta.CurrData
;




invariant "rule_221"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != i
)
end end ;




invariant "rule_222"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.Collecting = false
)
end ;




invariant "rule_223"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.PendReqSrc = i
)
end end ;




invariant "rule_224"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.FwdCmd != UNI_Get
)
end ;




invariant "rule_225"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i
)
end end ;




invariant "rule_226"

Sta.Dir.HeadVld = true -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_227"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.Dir.Pending = false
)
end ;




invariant "rule_228"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_229"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end end ;




invariant "rule_230"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != i
)
end ;




invariant "rule_231"
forall i : NODE do 
i != Home -> 
  (Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_232"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end ;




invariant "rule_233"

Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = true
;




invariant "rule_234"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck
)
end ;




invariant "rule_235"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Collecting = false
)
end end ;




invariant "rule_236"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end ;




invariant "rule_237"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end ;




invariant "rule_238"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != j
)
end end ;




invariant "rule_239"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Proc = j -> Sta.Proc[i].CacheState != CACHE_E
)
end end ;




invariant "rule_240"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Dir.HeadPtr != i
)
end end ;




invariant "rule_241"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.MemData = Sta.CurrData
;




invariant "rule_242"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState != CACHE_E -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_243"

Sta.Dir.Dirty = false -> Sta.Dir.InvSet[Home] = false
;




invariant "rule_244"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadPtr != j -> Sta.Proc[j].CacheState != CACHE_E
)
end ;




invariant "rule_245"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.InvMsg[j].Cmd != INV_Inv
)
end end ;




invariant "rule_246"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd = NODE_None
)
end ;




invariant "rule_247"

Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S
;




invariant "rule_248"

Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_Put
;




invariant "rule_249"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState = CACHE_I
)
end ;




invariant "rule_250"

Sta.Dir.HeadVld = true & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_FAck
;




invariant "rule_251"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != j
)
end ;




invariant "rule_252"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[j] = false
)
end end ;




invariant "rule_253"

Sta.Dir.Dirty = false -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_254"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_S
)
end ;




invariant "rule_255"

Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false
;




invariant "rule_256"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Dirty = false -> Sta.Proc[j].CacheState != CACHE_E
)
end ;




invariant "rule_257"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_Put
)
end ;




invariant "rule_258"

Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState = CACHE_I
;




invariant "rule_259"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.Collecting = false
)
end ;




invariant "rule_260"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_261"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Local = false
)
end ;




invariant "rule_262"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[i].Cmd != INV_Inv
)
end end ;




invariant "rule_263"

Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_FAck
;




invariant "rule_264"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_S
)
end ;




invariant "rule_265"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_Put
)
end ;




invariant "rule_266"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState = CACHE_S
;




invariant "rule_267"

Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S
;




invariant "rule_268"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = false -> Sta.Dir.HeadVld = false
)
end ;




invariant "rule_269"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Dirty = false -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end ;




invariant "rule_270"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_271"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.ShWbMsg.Proc != i
)
end end ;




invariant "rule_272"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_GetX
)
end ;




invariant "rule_273"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd = UNI_None
)
end ;




invariant "rule_274"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.HeadPtr != Home
)
end ;




invariant "rule_275"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Dir.InvSet[j] = false
)
end ;




invariant "rule_276"

Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX
;




invariant "rule_277"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false
)
end ;




invariant "rule_278"

Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.MemData = Sta.CurrData
;




invariant "rule_279"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState = CACHE_I
)
end end ;




invariant "rule_280"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_281"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Proc[Home].CacheState != CACHE_S
)
end end ;




invariant "rule_282"

Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false
;




invariant "rule_283"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadVld = false
)
end ;




invariant "rule_284"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end ;




invariant "rule_285"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_Inv
)
end ;




invariant "rule_286"

Sta.Dir.Pending = true & Sta.Dir.Dirty = false -> Sta.Proc[Home].CacheState = CACHE_I
;




invariant "rule_287"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv
)
end ;




invariant "rule_288"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end end ;




invariant "rule_289"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end ;




invariant "rule_290"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX
)
end end ;




invariant "rule_291"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.MemData = Sta.PrevData
)
end ;




invariant "rule_292"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false
)
end ;




invariant "rule_293"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.Proc[j].ProcCmd != NODE_Get
)
end ;




invariant "rule_294"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadPtr = i -> Sta.MemData = Sta.CurrData
)
end ;




invariant "rule_295"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_296"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end ;




invariant "rule_297"

Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put
;




invariant "rule_298"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end ;




invariant "rule_299"
forall j : NODE do 
j != Home -> 
  (Sta.Proc[j].ProcCmd = NODE_None -> Sta.Proc[j].InvMarked = false
)
end ;




invariant "rule_300"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX
)
end ;




invariant "rule_301"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Dir.InvSet[j] = false
)
end end ;




invariant "rule_302"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false
)
end ;




invariant "rule_303"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX
)
end ;




invariant "rule_304"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.Proc[j].CacheState != CACHE_E
)
end end ;




invariant "rule_305"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd = UNI_Get
)
end end ;




invariant "rule_306"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_307"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Collecting = true
)
end ;




invariant "rule_308"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end ;




invariant "rule_309"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.Proc[j].InvMarked = false
)
end end ;




invariant "rule_310"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.Proc[j].InvMarked = false
)
end end ;




invariant "rule_311"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_312"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != Home
)
end ;




invariant "rule_313"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState = CACHE_I
)
end ;




invariant "rule_314"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = false -> Sta.FwdCmd != UNI_GetX
)
end ;




invariant "rule_315"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_S
)
end ;




invariant "rule_316"
forall j : NODE do 
j != Home -> 
  (Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end ;




invariant "rule_317"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.InvSet[i] = true
)
end ;




invariant "rule_318"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.PendReqSrc != j
)
end end ;




invariant "rule_319"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[i].Cmd != INV_InvAck
)
end end ;




invariant "rule_320"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_321"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb
)
end ;




invariant "rule_322"

Sta.Dir.Local = true & Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState != CACHE_I
;




invariant "rule_323"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX
)
end ;




invariant "rule_324"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.InvMsg[j].Cmd != INV_InvAck
)
end end ;




invariant "rule_325"
forall i : NODE do 
i != Home -> 
  (Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_E
)
end ;




invariant "rule_326"
forall i : NODE do 
i != Home -> 
  (Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false
)
end ;




invariant "rule_327"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_GetX
)
end ;




invariant "rule_328"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E
)
end ;




invariant "rule_329"
forall i : NODE do 
i != Home -> 
  (Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Collecting = true
)
end ;




invariant "rule_330"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false
)
end ;




invariant "rule_331"
forall i : NODE do forall j : NODE do 
i != j & i != Home & j != Home  -> 
  (Sta.UniMsg[i].Cmd = UNI_Get & Sta.UniMsg[i].Proc = j -> Sta.FwdCmd != UNI_GetX
)
end end ;




invariant "rule_332"
forall i : NODE do 
i != Home -> 
  (Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX
)
end ;




invariant "rule_333"
forall i : NODE do 
i != Home -> 
  (Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false
)
end ;
