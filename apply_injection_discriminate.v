From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

Example apply_ex1:forall P Q:Prop,
(P->Q)->P->Q.
Proof.
  intros P Q P_imply_Q P_holds.
  (*apply P_imply_Q in P_holds.*) (* 正向推理 结果为将P_holds变为Q*)
  apply P_imply_Q.
  apply P_holds.
Qed.


Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.  Qed.


Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

Theorem trans_eq_2 : forall (X:Type) (n m o p : X),
  n = m -> m = p -> p = o -> n = o.
Proof.
Admitted.

Example trans_eq_example'_2 : forall (a b c d e f h i: nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [e;f] = [h;i] ->
     [a;b] = [h;i].
Proof.
  intros a b c d e f h i eq1 eq2 eq3.
  apply trans_eq_2 with (m:=[c;d]) (p:=[e;f]).
  apply eq1. apply eq2. apply eq3.
Qed.

(*通过在此处编写injection H
我们命令Coq使用构造子的单射性来产生所有它能从H所推出的等式
每一个产生的等式都作为一个前件附加在目标上
在这个例子中 附加了前件n=m*)
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

(*爆炸原理可能令你费解
那么请记住上述证明并不肯定其后件
而是说明:倘若荒谬的前件成立 则会得出荒谬的结论*)
Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

