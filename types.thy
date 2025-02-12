theory types
  imports 
    "Separation_Logic_Imperative_HOL.Sep_Main"
begin

subsection \<open>Types\<close>

text \<open>Access by value or by reference\<close>
datatype 'a type =
  Val "'a" 
| Ref "'a type ref option"

fun type_encode :: "'a::countable type \<Rightarrow> nat" where                          
  "type_encode (Val x) =   2 * to_nat x"
| "type_encode (Ref p) = 1+2 * to_nat p"

lemma inj_type_val_val: "type_encode (Val x) = type_encode (Val y) \<Longrightarrow> x = y" 
  by simp
lemma inj_type_ptr_ptr: "type_encode (Ref x) = type_encode (Ref y) \<Longrightarrow> x = y" 
  by simp
lemma neq_type_val_ptr: "type_encode (Val x) \<noteq> type_encode (Ref y)"
  by (simp add: double_not_eq_Suc_double)

lemma inj_type_encode: "inj type_encode"
  apply (rule injI)
  apply (case_tac x, case_tac y)
  apply (metis inj_type_val_val)
  apply (metis neq_type_val_ptr)
  apply (metis inj_type_ptr_ptr neq_type_val_ptr type.exhaust)
  done

instance type :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "type_encode"])
  apply (simp add: inj_eq inj_type_encode)
  ..


subsection \<open>Structural Nodes\<close>
text \<open>Structural nodes. Represents memory in the computer as either variables or 
      recursively nested C-style structures\<close>
(* Values are abstract types with size 1. To possibly introduce types with varying sizes,
   we could encode different types as lists of values, with each value representing 
   a byte in the machine representation of the type. *)
(* Since lists are countable, 'a can easily be a list type *)
datatype 'a struct_node =
  Member  'a
| Struct "'a struct_node list" (* This is a laid-out node. Defined later. *)

text \<open>We account for to_nat having different definitions when operating on a value 
      or lists by encoding members and structs with distinct parities.\<close>
fun struct_node_encode :: "'a::countable struct_node \<Rightarrow> nat" where
  "struct_node_encode (Member x)  =   2 * to_nat x" 
| "struct_node_encode (Struct xs) = 1+2 * to_nat(map struct_node_encode xs)" 

text \<open>(Struct xs) and (Member y) have different parities,
      so their encodings never coincide\<close>
lemma struct_neq_value: 
  "struct_node_encode (Struct xs) \<noteq> struct_node_encode (Member y)"
proof
  assume "struct_node_encode (Struct xs) = struct_node_encode (Member y)"
  hence "1+2 * to_nat (map struct_node_encode xs) = 2 * to_nat y"
    by simp
  thus False
    by presburger
qed

lemma inj_struct_node_encode:
  "inj struct_node_encode"
proof (rule injI)
  fix a b :: "'a struct_node"
  show "struct_node_encode a = struct_node_encode b \<Longrightarrow> a = b"
  text \<open>Induction hypothesis required in the Struct = Struct case\<close>
  proof (induction a arbitrary: b)
    case (Member x)
    then show ?case
    proof (cases b)
      case (Member y)
      then show ?thesis
        using Member.prems by simp
    next
      case (Struct ys)
      then show ?thesis
        by (metis Member struct_neq_value)
    qed
  next
    case (Struct xs)
    then show ?case
    proof (cases b)
      case (Member y)
      then show ?thesis
        using Struct.prems struct_neq_value by auto
    next
      case (Struct ys)
      assume "struct_node_encode (Struct xs) = struct_node_encode b"
      and    "b = Struct ys"
      hence "struct_node_encode (Struct xs) = struct_node_encode (Struct ys)"
         by simp
      hence "xs = ys"
        using Struct.IH by (induction xs ys rule: list_induct2', simp_all)
      thus ?thesis
        by (simp add: \<open>b = Struct ys\<close>)
    qed
  qed
qed

text \<open>Structural nodes can be represented abstractly on 
      the heap. Hence they can be indexed only by indexing 
      their elements and not by pointer arithmetic.\<close> 
instance struct_node :: (heap) heap
  apply (rule heap_class.intro)
  apply (rule countable_classI [of "struct_node_encode"])
  apply (simp add: inj_eq inj_struct_node_encode)
  ..

subsection \<open>Laid-out Nodes\<close>
text \<open>Laid-out nodes have an array-like layout and admit pointer arithmetic\<close>

text \<open>From GillianRust: 
A laid-out node is a pair composed of a sized type (called indexing type) and a list of structural
nodes each annotated with the range it occupies in multiples of the size of the indexing type\<close>

(* PROBLEM: struct_nodes can only be values and not struct node references *)
type_synonym 'a laid_out_node =  "'a struct_node list"

(* TODO: Rename to better reflect the type's existence only on heaps *)
type_synonym 'a laid_out_impl  = "'a struct_node array"


subsection \<open>Interaction with Heap\<close>
type_synonym 'a node = "'a type laid_out_node type"

text \<open>Allocate laid-out nodes in contiguous memory\<close>
definition alloc_laid_out :: "'a::heap laid_out_node \<Rightarrow> 'a laid_out_impl Heap" where
  "alloc_laid_out xs = Array.of_list xs"

text \<open>Define struct allocation using the singleton case of laid-out nodes\<close>
definition alloc_struct :: "'a::heap struct_node \<Rightarrow> 'a laid_out_impl Heap" where
  "alloc_struct x = alloc_laid_out [x]"

definition laid_out_from_list :: "'a node list \<Rightarrow> 'a node" where
  "laid_out_from_list xs \<equiv> Val [Struct []]"

text \<open>Takes value and pointer and returns a node containing these values in a structure\<close>
fun lseg_new :: "'a node \<Rightarrow> 'a node \<Rightarrow> 'a node" where
  "lseg_new (Val x) (Ref p) = Val [Struct x]" (* TODO: encode pointer in list *)
| "lseg_new _ _ = undefined" (* Must have pointer to next cell *)

fun lseg :: "'a::heap node list \<Rightarrow> 'a node \<Rightarrow> 'a node \<Rightarrow> assn" where
  "lseg [] (Ref p) (Ref s) = \<up>(p=s)" 
| "lseg (x#xs) (Ref (Some p)) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r (lseg_new x q) * lseg xs q s)"
| "lseg _ _ _ = false"

(*
fun lseg :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> 'a node ref option \<Rightarrow> assn"
  where
  "lseg [] p s = \<up>(p=s)"
| "lseg (x#l) (Some p) s = (\<exists>\<^sub>Aq. p \<mapsto>\<^sub>r Node x q * lseg l q s)"
| "lseg (_#_) None _ = false"
*)

end

