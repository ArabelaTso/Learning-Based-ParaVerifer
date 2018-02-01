# LB-CMP

## Introduction

LB-CMP is an automatic learning-based parameterized verifier. 

## Background

We automate the method "parameterized abstraction and guard strengthening", also know as **CMP**, the abbreviation of its authors. Since 2004, Chou *et. al* proposed this method and carried it out by hand (with the help of model checker), no one has  automated it until now. The hardest part of automating its process is how to formulate sufficient auxiliary invariants, which is originally relies on researchers analysis of protocol description. Thus, we propose a learning-based framework, LB-CMP (**L**earning-**B**ased **CMP**) which combines with data mining techniques without understanding the detailed protocol description. 

It works as follow:

- Learning association rules from reachable set of protocols.
- Selecting auxiliary invariants from association rules.
- Abstracting protocols.
- Strengthening abstracted protocols.

## Files in each folder

(Use '**PN**' to represent the specified protocol name)

- **PN.txt**: which is the output of Muprhi, with parameter '-ta'
  - Due to the file size limit of Github, we do not upload reachable sets of Flash and Flash-no-data protocol. They can be printed using [CMurphi](http://mclab.di.uniroma1.it/site/index.php/software/18-cmurphi).

- **PN.csv**: which is the dataset with all states. 
- **Rules_PN.txt**: association rules learned from PN.csv.
- **candidate_rules.txt**:  candidate rules we select from Rules_PN.txt
- **Inv_PN.txt**: In fact, this file contains local truth, because we only use specific parameter (e.g. 4 or 5) to filter apparently local truths and spurious invariants. Once the 'invariant' in this file has been used to strength abstracted protocol, it will also be verified to make sure it is not a spurious one.
- **ABS_PN.m**: The abstracted protocol, run it to see whether the original properties have been broken.
- **ABS_PN-with-lemmas.m**: The abstracted protocol with used auxiliary invariants. Run it to see whether used invariants have been broken.
- **lemma_used.txt**: Record for the used auxiliary invariants.


## Result

| Protocol name | # Node | # States | # Association rules | # Candidate Rules | # Invariants | # Invariants used for strengthening | # States of abstracted protocol | Time for association rules learning | Time for selecting invariants |
| :-----------: | :----: | :------: | :-----------------: | :---------------: | :----------: | :---------------------------------: | :-----------------------------: | :---------------------------------: | :---------------------------: |
|     Moesi     |   2    |    6     |         147         |        19         |      2       |                  0                  |                7                |               0.004 s               |            5.176 s            |
|     Mesi      |   2    |    5     |         80          |        25         |      4       |                  1                  |                5                |               0.003 s               |            4.676 s            |
|   MutualEx    |   2    |    12    |         450         |        27         |      16      |                  5                  |               18                |               0.009 s               |            8.042 s            |
|    German     |   2    |   852    |        21202        |        369        |     239      |                 30                  |              1314               |               1.433 s               |           88.714 s            |
| Flash-no-data |   3    |  784637  |       224946        |       2805        |     449      |                 158                 |             9674424             |             8930.652 s              |           631.460 s           |
|     Flash     |   3    | 1350226  |       381528        |       3263        |     651      |                 333                 |            26962920             |             21909.092 s             |           696.654 s           |

