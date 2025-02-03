theory linkedlist
  imports "../Separation_Logic_Imperative_HOL/Sep_Main"
begin

datatype 'a node = Node "'a" "'a node ref option"


text \<open>Encoding to natural numbers, as required by Imperative/HOL. Heaps accept arbitrary nats.\<close>
fun
  node_encode :: "'a::heap node \<Rightarrow> nat"
where                          
  "node_encode (Node x r) = to_nat (x, r)"

instance node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "node_encode"])
  apply (case_tac x, simp_all, case_tac y, simp_all)
  ..

text \<open>Takes a list, l, a pointer to head l, and a pointer to last l, and returns 
      the pointer model of the list\<close>
fun lseg :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option \<Rightarrow> assn"
  where
  "lseg [] p s = \<up>(p=s)"
| "lseg (x#l) (Some p) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * lseg l q s)"
| "lseg (_#_) None _ = false"

text \<open>Pointer structure where first and last pointer are both null clearly represents empty list\<close>
lemma lseg_empty: "lseg l None None = \<up>(l=[])"
  by (cases l, simp_all)

text \<open>Appending an element to the front of a mathematical list is identical to 
      creating a new node pointing to the rest of the linked list\<close>
lemma lseg_split [simp]: "lseg (x#xs) p q = (\<exists>\<^sub>Ar n. r \<mapsto>\<^sub>r (Node x n) * lseg xs n q * \<up>(p=Some r))"
proof (cases p)
  case None
  then show ?thesis by simp_all
next 
  case (Some a)
  show ?thesis using \<open>p = Some a\<close>
    apply simp_all
  proof (rule ent_iffI)
    let ?lhs = "(\<exists>\<^sub>Aqa. a \<mapsto>\<^sub>r Node x qa * lseg xs qa q)"
    let ?rhs = "(\<exists>\<^sub>Ar n. r \<mapsto>\<^sub>r Node x n * lseg xs n q * \<up> (a = r))"
    show "?lhs \<Longrightarrow>\<^sub>A ?rhs" by solve_entails
    show "?rhs \<Longrightarrow>\<^sub>A ?lhs" by solve_entails
  qed
qed

text \<open>Prepending is correct\<close>
lemma lseg_prepend: "p\<mapsto>\<^sub>rNode x q * lseg l q s \<Longrightarrow>\<^sub>A lseg (x#l) (Some p) s"
  by sep_auto

text \<open>Appending is correct\<close>
lemma lseg_append: "lseg l p (Some s) * s\<mapsto>\<^sub>rNode x q \<Longrightarrow>\<^sub>A lseg (l@[x]) p q"
proof (induction l arbitrary: p)
  case Nil thus ?case by sep_auto
next
  case (Cons y l)
  show ?case
  proof (cases p)
    case None then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis
      apply sep_auto
      apply (rule ent_frame_fwd[OF Cons.IH])
      apply frame_inference
      by solve_entails
  qed
qed

text \<open>Concatenation of two lists is correct\<close>
lemma lseg_concat: "lseg l1 p q * lseg l2 q r \<Longrightarrow>\<^sub>A lseg (l1@l2) p r"
proof (induct l1 arbitrary: p)
  case Nil thus ?case by simp
next
  case (Cons x l1)
  show ?case
    apply simp
    apply sep_auto
    apply (rule ent_frame_fwd[OF Cons.hyps])
    apply frame_inference
    by solve_entails
qed

text \<open>Splitting of two lists is correct\<close>
lemma lseg_splits: "lseg (l1@l2) p r \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg l1 p q * lseg l2 q r"
proof (induct l1 arbitrary: p)
  case Nil thus ?case by sep_auto
next
  case (Cons x l1)

  have "lseg ((x # l1) @ l2) p r 
    \<Longrightarrow>\<^sub>A \<exists>\<^sub>App n. pp \<mapsto>\<^sub>r Node x n * lseg (l1 @ l2) n r * \<up> (p = Some pp)"
    by simp
  also have "\<dots> \<Longrightarrow>\<^sub>A 
    \<exists>\<^sub>App n q. pp \<mapsto>\<^sub>r Node x n 
      * lseg l1 n q 
      * lseg l2 q r 
      * \<up>(p = Some pp)"
    apply (intro ent_ex_preI)
    apply clarsimp
    apply (rule ent_frame_fwd[OF Cons.hyps])
    apply frame_inference
    apply sep_auto
    done
  also have "\<dots> \<Longrightarrow>\<^sub>A \<exists>\<^sub>Aq. lseg (x#l1) p q * lseg l2 q r"
    by sep_auto
  finally show ?case .
qed

lemma lseg_split_equiv: "(lseg (l1@l2) p r) = (\<exists>\<^sub>Aq. lseg l1 p q * lseg l2 q r)" 
  (is "?lhs = ?rhs")
proof (rule ent_iffI)
  show "?lhs \<Longrightarrow>\<^sub>A ?rhs" by (rule lseg_splits)
  show "?rhs \<Longrightarrow>\<^sub>A ?lhs" by (simp add: ent_ex_preI lseg_concat)
qed

end
