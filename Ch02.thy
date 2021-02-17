theory Ch02
  imports Main
begin

(* Exercise 2.1 *)
value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "(1 - (2 :: nat))"
value "1 - (2 :: int)"
value "[a,b] @ [c,d]"

(* Exercise 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m  n)"

lemma add_assoc: "add (add m n) p = add m (add n p)"
  apply (induction m)
  apply (auto)
  done

lemma add_0[simp]: "add n 0 = n"
  apply (induction n)
  apply (auto)
  done

lemma add_succ[simp]: "add n (Suc m) = Suc (add n m)"
  apply (induction n)
  apply (auto)
  done

lemma add_comm: "add m n = add n m"
  apply (induction m)
  apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

value "double 42"

lemma double_add: "double m = add m m"
  apply (induction m)
  apply (auto)
  done

(* Exercise 2.3 *)
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] n = 0" |
"count (x # xs) n = (if x = n then Suc (count xs n) else count xs n)"

theorem "count xs x \<le> length xs"
  apply (induction xs)
  apply (auto)
  done

(* Exercise 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]" |
"snoc (x # xs) y = x # snoc xs y"

value "snoc [] a"
value "snoc [a,b,c,d] e"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

value "rerverse []"
value "reverse [a,b,c]"

lemma rev_snoc[simp]: "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
  apply (auto)
  done

theorem "reverse (reverse xs) = xs"
  apply (induction xs)
  apply (auto)
  done

(* Exercise 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + (sum_upto n)"

value "(sum_upto 3)"
value "(sum_upto 10)"

lemma "sum_upto n = n * (n+1) div 2"
  apply (induction n)
  apply (auto)
  done

(* Exercise 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

value "(Node (Node Tip a Tip) b (Node Tip c Tip))"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node t1 x t2) = x # (contents t1) @ (contents t2)"

value "contents ((Node (Node Tip a Tip) b (Node Tip c Tip)))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node t1 x t2) = x + (sum_tree t1) + (sum_tree t2)"

value "sum_tree (Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip))"

lemma "sum_tree t = sum_list (contents t)"
  apply (induction t)
  apply (auto)
  done

(* TODO: 2.7 *)

end
