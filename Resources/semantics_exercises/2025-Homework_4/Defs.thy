theory Defs
  imports Main "HOL-IMP.Vars"
begin

declare [[names_short]]

type_synonym ('q,'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word :: " ('q,'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" for \<delta> where
  empty: " word \<delta> q [] q"
| prepend: "\<lbrakk>\<delta> p l ph; word \<delta> ph ls q\<rbrakk> \<Longrightarrow> word \<delta> p (l # ls) q"

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 (LOADI n) _ stk = Some (n # stk)"
| "exec1 (LOAD x) s stk = Some (s(x) # stk)"
| "exec1 ADD _ stk = (case stk of
    a # b # c \<Rightarrow> Some ((a + b) # c)
  | _ \<Rightarrow> None)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stk = Some stk"
| "exec (i # ins) s stk = (case exec1 i s stk of
    Some stk \<Rightarrow> exec ins s stk
  | None \<Rightarrow> None)"

lemma exec_append[simp]:
  "exec (ins1 @ ins2) s stk = (case exec ins1 s stk of
    Some stk \<Rightarrow> exec ins2 s stk
  | None \<Rightarrow> None)"
  apply(induction ins1 arbitrary: stk)
   apply (auto split: option.split)
  done

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  apply(induction a arbitrary: stk)
    apply (auto)
  done

definition "correct a ins \<equiv> \<forall>s stk. exec ins s stk = Some (aval a s # stk)"


consts prod :: "('q\<^sub>1,'l) lts \<Rightarrow> ('q\<^sub>2,'l) lts \<Rightarrow> 'q\<^sub>1\<times>'q\<^sub>2 \<Rightarrow> 'l \<Rightarrow> 'q\<^sub>1\<times>'q\<^sub>2 \<Rightarrow> bool"


end