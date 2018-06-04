# LB-CMP

## Introduction

LB-CMP is an automatic learning-based parameterized verifier. 

## Background

We automate the method "parameterized abstraction and guard strengthening", also know as **CMP**, the abbreviation of its authors. Since 2004, Chou *et. al* proposed this method and carried it out by hand (with the help of model checker), no one has  automated it until now. The hardest part of automating its process is how to formulate sufficient auxiliary invariants, which is originally relies on researchers analysis of protocol description. Thus, we propose a learning-based framework, L-CMP (**L**earning-based **CMP**) which combines with data mining techniques without understanding the detailed protocol description. 

It works as follow:

- Learning association rules from reachable set of protocols.
- Selecting auxiliary invariants from association rules.
- Abstracting protocols.
- Strengthening abstracted protocols.

## Files in each folder

(Use '**PN**' to represent the specified protocol name)

- **PN.m**: the protocol in Murphi code


- **PN.txt**: output from Muprhi, with parameter '-ta'
  - Due to the file size limit of Github, we do not upload reachable sets of Flash and Flash-no-data protocol. They can be printed using [CMurphi](http://mclab.di.uniroma1.it/site/index.php/software/18-cmurphi).

- **PN.csv**: which is the dataset with all states. 
- **assoRules.txt**: association rules
- **invs.txt**:  Invariants without selection
- **aux_invs.txt**: Auxiliary invariants
- **ABS_PN.m**: Protocols after strengthening and abstraction
- **lemma_used.txt**: Record for the used auxiliary invariants.


## Result

| protName | \# assoRules | \# auxInvs | \# usedF | Time (s)  | result |
| -------- | ------------ | ---------- | -------- | --------- | ------ |
| MOESI    | 736          | 20         | 5        | 24.744    | ☑      |
| MESI     | 144          | 16         | 5        | 24.412    | ☑      |
| MutualEx | 656          | 12         | 3        | 89.869    | ☑      |
| Mutdat   | 540          | 12         | 6        | 19.703    | ☑      |
| German   | 21202        | 448        | 8        | 85.418    | ☑      |
| Flash    | 358710       | 1636       | 327      | 41371.023 | ☑      |


