theory ex_4_1
  imports Main
begin

thm conjunct2

lemma assumes T: "∀ x y. T x y ∨ T y x"
      and A: "∀ x y. A x y ∧ A y x --> x = y"
      and TA: "∀ x y. T x y --> A x y" 
      and "A x y"
    shows "T x y"
proof (rule ccontr) (*TODO mention in the notes*)
  assume nTxy: "¬ T x y"
  hence Tyx: "T y x" using T by blast
  hence Ayx: "A y x" using TA by blast (*TODO why it throw error when I write "this" inside facts of "using" *)
  hence "x = y" using A assms(4) by blast
  hence Txy: "T x y" using Tyx by blast
  show "False" using nTxy Txy by blast (*TODO why by (rule nTxy[OF Txy]) does not work *)
qed


end