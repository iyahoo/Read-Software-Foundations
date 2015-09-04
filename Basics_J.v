Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Eval simpl in (next_weekday friday). 
Eval simpl in (next_weekday (next_weekday saturday)). 

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true    
  end.

Example test_negb1 :
  (negb true) = false.
Proof. simpl. reflexivity. Qed. 

Example test_negb2 :
  (negb false) = true.
Proof. simpl. reflexivity. Qed.
  
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Example test_andb1 :
  (andb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb2 :
  (andb true false) = false.
Proof. simpl. reflexivity. Qed. 

Example test_andb3 :
  (andb false true) = false.
Proof. simpl. reflexivity. Qed. 

Example test_andb4 :
  (andb false false) = false.
Proof. simpl. reflexivity. Qed. 

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1 :
  (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 :
  (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3 :
  (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 :
  (orb false false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise nandb *)

Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

Example test_nandb1:
  (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2:
  (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3:
  (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4:
  (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1 with
    | true => andb b2 b3
    | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true). 
Check negb.
Check andb. (* : bool -> bool -> bool *)

Module Playground1. 

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.

End Playground1.

Definition play_minustwo (n : Playground1.nat) : Playground1.nat :=
  match n with
    | Playground1.O => Playground1.O
    | Playground1.S Playground1.O => Playground1.O
    | Playground1.S (Playground1.S n') => n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Example test_evenb1 :
  (evenb O) = true.
Proof. simpl. reflexivity. Qed.

Example test_evenb2 :
  (evenb (S (S (S O)))) = false. 
Proof. simpl. reflexivity. Qed.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1 :
  (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2 :
  (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.

  Eval simpl in (plus (S (S O)) (S (S (S O)))).

  Example test_plus1 :
    plus (S (S O)) (S (S (S O))) = 5.
  Proof. simpl. reflexivity. Qed.

  Example test_plus2 :
    plus O (S (S (S O))) = 3.
  Proof. simpl. reflexivity. Qed.
  
  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1 :
    mult (S (S O)) (S (S (S O))) = 6.
  Proof. simpl. reflexivity. Qed.

  Example test_mult2 :
    mult (S (S (S (S O)))) (S O) = 4.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | S _, O => n
      | S n', S m' => minus n' m'
    end.

  Example test_minus1 :
    minus (S (S (S O))) (S O) = 2.
  Proof. simpl. reflexivity. Qed.

  Example test_minus2 :
    minus (S (S (S (S O)))) (S (S (S (S (S O))))) = 0.
  Proof. simpl. reflexivity. Qed.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S power' => mult base (exp base power')
  end.

Example test_exp1 :
  exp (S O) O = 1.
Proof. simpl. reflexivity. Qed.

Example test_exp2 :
  exp (S (S (S O))) (S (S O)) = 9.
Proof. simpl. reflexivity. Qed.

(* Exercise factorial *)

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1 :
  (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 :
  (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


