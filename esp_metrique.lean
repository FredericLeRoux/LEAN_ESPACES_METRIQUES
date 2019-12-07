import tactic
import data.real.basic
import data.set

------------
-- ESSAIS --
------------
open set

example (α : Type) (s : set (set α)) : ∀ t : set α, t ∈ s →  t ⊆ sUnion s :=
begin
  --library_search,
  intro h,
  exact subset_sUnion_of_mem,
end


-----------
-- DEBUT --
-----------

/-- Une structure d'espace métrique sur un type X -/
class espace_metrique (X : Type) :=
(dist : X → X → ℝ)
(dist_pos : ∀ x y, dist x y ≥ 0)
(sep : ∀ x y, dist x y = 0 ↔ x = y)
(triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)


open espace_metrique

/-- Fonction distance avec le type en argument explicite -/
def dist' (X : Type) [espace_metrique X] : X → X → ℝ := λ x y, dist x y

notation `d` := dist
notation `d_[` X `]` := dist' X


----------------------------------------------------
section fondements
variables {X : Type} [espace_metrique X]

/-- `boule x r` est la boule ouverte de centre `x` et de rayon `r` -/
def boule (x : X) (r : ℝ)  := {y | dist x y < r}


lemma mem_boule (x : X) (r : ℝ) : ∀ y, y ∈ boule x r ↔ dist x y < r := 
assume y, iff.rfl

variables (x y : X) (r : ℝ)
#check boule x r
#check @boule X _ x r
example : d_[X] x y = d x y :=
begin
  refl,
end

/-- Une partie d'un espace métrique `X` est ouverte si elle contient une boule ouverte de rayon 
strictement positif autour de chacun de ses points. -/
def ouvert (A : set X) := ∀ x ∈ A, ∃ r > 0, boule x r ⊆ A

lemma boule_est_ouverte : ∀ x : X, ∀ r > 0, ouvert (boule x r) :=
begin
  intros x r r_pos y y_in, -- on déroule les définitions,
  -- on se retrouve avec un point y dans la boule
  -- de centre x et de rayon r, et on cherche une boule autour de y qui soit incluse
  -- dans boule x r
  use  r - d x y, -- le rayon candidat
  rw exists_prop,
  split,
  { -- La ligne suivante peut être remplacée par n'importe laquelle des trois lignes qui la suivent
    simp [boule] at y_in,
    --change d x y < r at y_in,
    --rw mem_boule at y_in,
    --unfold boule at y_in, rw set.mem_set_of_eq at y_in,
    linarith }, -- le rayon est bien strictement positif
  { -- La ligne suivante est optionnelle, elle sert  à expliciter le but
    -- change ∀ z, z ∈ boule y (r - d x y) → z ∈ boule x r,
    intros z z_in,
    rw mem_boule at *,
    have clef : d x z ≤ d x y + d y z, from triangle x y z,
    linarith }, -- et l'inégalité triangulaire permet de montrer l'inclusion des boules
end




-- Lemme de théorie des ensembles - finalement non utilisé
lemma inclusion_transitive {Y : Type} {A B C : set Y} : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intros AB BC a a_app_A,
  exact BC (AB a_app_A),  
end




lemma union_ouverts_est_ouvert (I : set (set X)) : (∀ O ∈ I, ouvert O) → ouvert (⋃₀ I) :=
begin
  intro O_ouverts, -- les ensembles O sont ouverts
  intros x x_dans_union, -- un point dans l'union
  cases x_dans_union with O x_app_O', -- donc dans l'un des ouverts O
  rw exists_prop at x_app_O',
  cases x_app_O' with O_app_I x_app_O,
  have O_ouvert : ouvert O, from (O_ouverts O) O_app_I,
  have existe_r, from O_ouvert x x_app_O, -- O est ouvert, ce qui fourni un rayon
  cases existe_r with r hr,
  rw exists_prop at hr,
  cases hr with r_positif boule_dans_O,
  use r, -- on utilise ce rayon pour montrer que l'union est ouverte
  rw exists_prop,
  split, assumption, -- il est bien positif
  have O_dans_union : O ⊆ ⋃₀ I, from by exact subset_sUnion_of_mem O_app_I,
  -- Les deux lignes suivantes démontrent, dans notre contexte, 
  -- que l'inclusion est transitive, on peut les remplacer par 
  -- la dernière ligne commentée
  intros y H,
  exact O_dans_union (boule_dans_O H),
  -- exact inclusion_transitive boule_dans_O O_dans_union,
end


-- on montre que l'intersection de deux ouvert est un ouvert, 
-- puis intersection finie par récurrence (ou directement)
lemma intersection_deux_ouverts_est_ouvert : ∀ O₁ O₂ : set X, (ouvert O₁ ∧ ouvert O₂) → ouvert (O₁ ∩ O₂) :=
begin
sorry
end


variable β : Type
lemma intersection_ouverts_est_ouvert  [fintype β] {O : β → set X}
  (h : ∀ i, ouvert (O i)) : ouvert (⋂ i, O i) :=
begin
sorry
end

-- comment formuler que X et ∅ sont ouverts ?


-- def topo de l'intérieur. Caractérisation métrique.

-- Voisinages ?

end fondements



------------------------------------------------
section continuite
variables {X Y : Type} [espace_metrique X] [espace_metrique Y]

-- dans la définition suivante les `d_[X]` et `d_[Y]` sont cosmétiques, `d` seul marche aussi bien

def continue_en (f : X → Y) (x₀ : X) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x x₀ < δ → d_[Y] (f x) (f x₀) < ε   

def continuite (f:X → Y) := ∀ x : X, continue_en f x

-- Notations f continue, f continue_au_point x

end continuite