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

(* Exercise 2.7 *)
datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Leaf x) = Leaf x" |
"mirror (Node t1 x t2) = Node (mirror t2) x (mirror t1)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node t1 x t2) = x # pre_order t1 @ pre_order t2"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node t1 x t2) = post_order t1 @ post_order t2 @ [x]"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply (auto)
  done

(* Exercise 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse x [] = []" |
"intersperse x (y # ys) = [y, x] @ intersperse x ys"

value "intersperse a [a,b,c]"
value "intersperse 1 [1,2,3] :: int list"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
  apply (auto)
  done

(* Exercise 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add m n"
  apply (induction m arbitrary: n)
  apply (auto)
  done

(* Exercise 2.10 *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node t1 t2) = 1 + (nodes t1) + (nodes t2)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

(* Exercise 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var n = n" |
"eval (Const c) _ = c" |
"eval (Add l r) n = (eval l n) + (eval r n)" |
"eval (Mult l r) n = (eval l n) * (eval r n)"

value "eval (Add (Mult (Const 2) Var) (Const 3)) i"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] _ = 0" |
"evalp [a0] _ = a0" |
"evalp (ai # as) x = ai + x * (evalp as x)"

value "evalp [4,2,-1,3] 2"

(* TODO: fun coeffs :: "exp \<Rightarrow> int list" *)

(* TODO: theorem evalp_coeffs: "evalp (coeffs e) x = eval e x" *)

end
