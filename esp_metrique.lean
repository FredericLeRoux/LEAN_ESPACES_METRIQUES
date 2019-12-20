import tactic
import data.real.basic
import data.set

------------
-- ESSAIS --
------------
open set

-----------
-- DEBUT --
-----------

/-- Une structure d'espace métrique sur un type X -/
class espace_metrique (X : Type) :=
(dist : X → X → ℝ)
(dist_pos : ∀ x y, dist x y ≥ 0)
(sep : ∀ x y, dist x y = 0 ↔ x = y)
(sym : ∀ x y, dist x y = dist y x)
(triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)


open espace_metrique

/-- Fonction distance avec le type en argument explicite -/
def dist' (X : Type) [espace_metrique X] : X → X → ℝ := λ x y, dist x y

notation `d` := dist
notation `d_[` X `]` := dist' X


----------------------------------------------------
section fondements
----------------------------------------------------

variables {X : Type} [espace_metrique X]

lemma dist_x_x_eq_zero  (x:X) : d x x = 0 := 
begin
  have h: x=x, from rfl,
  exact (sep x x).2 h,
end

/-- `boule x r` est la boule ouverte de centre `x` et de rayon `r` -/
def boule (x : X) (r : ℝ)  := {y | dist x y < r}

/-- appartenir à une boule équivaut à une inégalité -/
lemma mem_boule (x : X) (r : ℝ) : ∀ y, y ∈ boule x r ↔ dist x y < r := 
assume y, iff.rfl

/-- Une boule de rayon >0 contient son centre --/
lemma centre_mem_boule (x : X) (r : ℝ) : r > 0 → x ∈ boule x r :=
begin
intro r_pos,
simp [boule],
rw (dist_x_x_eq_zero x),
assumption,
end



variables (x y : X) (r : ℝ)
#check boule x r
#check @boule X _ x r

/-- Une partie d'un espace métrique `X` est ouverte si elle contient une boule ouverte de rayon 
strictement positif autour de chacun de ses points. -/
def ouvert (A : set X) := ∀ x ∈ A, ∃ r > 0, boule x r ⊆ A

/-- Les boules sont ouvertes -/
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

/-- Une union d'ouverts d'un espace métrique est un ouvert -/
lemma union_ouverts_est_ouvert (I : set (set X)) : (∀ O ∈ I, ouvert O) → ouvert (⋃₀ I) :=
begin
  -- Supposons que tous les O dans I sont ouverts.
  intro O_ouverts,
  -- Soit x un point d'un des O dans I
  rintro x ⟨O, O_app_I, x_app_O⟩,
  -- Comme O est ouvert, il existe r > 0 tel que B(x, r) ⊆ O
  obtain ⟨r, r_positif, boule_dans_O⟩ : ∃ r > 0, boule x r ⊆ O,
    from (O_ouverts O) O_app_I x x_app_O,
  -- Montrons que ce r convient 
  use [r, r_positif],
  -- Puisque  B(x, r) ⊆ O, il suffit de montrer que O ⊆ ⋃₀ I
  transitivity O, assumption,
  -- Or O est dans I.
  exact subset_sUnion_of_mem O_app_I
end

-- ** variante en λ-calcul - non utilisé
lemma union_ouverts_est_ouvert' (I : set (set X)) : (∀ O ∈ I, ouvert O) → ouvert (⋃₀ I) :=
assume O_ouverts x ⟨O, O_app_I, x_app_O⟩,
let ⟨r, r_positif, boule_dans_O⟩ := O_ouverts O O_app_I x x_app_O in
⟨r, r_positif, subset.trans boule_dans_O (subset_sUnion_of_mem O_app_I)⟩


/-- L'intersection de deux ouverts est un ouvert -/
lemma intersection_deux_ouverts_est_ouvert : ∀ O₁ O₂ : set X, ouvert O₁ →  ouvert O₂ → ouvert (O₁ ∩ O₂) :=
begin
  -- Soit x un point dans l'intersection,
  rintro O₁ O₂ ouvert_O₁ ouvert_O₂ x ⟨x_app_O₁,x_app_O₂⟩,
  -- le fait que O₁ et O₂ soient ouverts fournis deux nombres positifs
  obtain ⟨r₁,r₁_pos,boule_dans_O₁⟩ : ∃ r₁>0, boule x r₁ ⊆ O₁, from ouvert_O₁ x x_app_O₁,
  obtain ⟨r₂,r₂_pos,boule_dans_O₂⟩ : ∃ r₂>0, boule x r₂ ⊆ O₂, from ouvert_O₂ x x_app_O₂,
  -- Montrons que le minimum r des deux convient
  use min r₁ r₂, 
  rw exists_prop,
  -- Il est bien positif
  split, 
    by exact lt_min r₁_pos r₂_pos,
  -- Prenons un y dans la boule de rayon r
  intros y y_app_boule, 
  simp [boule] at y_app_boule,
  rcases y_app_boule with ⟨ineg_1,ineg_2⟩,
  -- il est dans O₁ et dans O₂ 
  have y_O₁ : y ∈ O₁, from boule_dans_O₁ ineg_1,
  have y_O₂ : y ∈ O₂, from boule_dans_O₂ ineg_2,
  -- donc dans l'intersection, comme voulu.
  exact and.intro y_O₁ y_O₂,
end

/-- L'espace total est ouvert -/
lemma total_ouvert : ouvert (univ : set X) :=
begin
  intros x hx,  
  use 1,
  rw exists_prop,
  split,
    exact zero_lt_one,
    exact subset_univ (boule x 1),
end

/-- L'intersection d'un nombre fini d'ouverts est un ouvert -/
--lemma intersection_ouverts_est_ouvert'  
--(I : set (set X)) : (finite I) (∀ O ∈ I, ouvert O) → ouvert (⋂₀ I) :=
--begin
  --tactic.unfreeze_local_instances,
  --rcases _inst_2 with ⟨Liste, Liste_exhaustive⟩,
  --sorry
--end

--{s : set β} {f : β → set α} (hs : finite s) :
--variables (β : Type) 
--lemma intersection_ouverts_est_ouvert  {s: set β} {O : β → set X} (hs: finite s) :
--  (∀ i, ouvert (O i)) → ouvert (⋂ i, O i) :=
--begin
--  set.finite.induction_on hs (sorry) (sorry)
  -- (λ _, by rw bInter_empty; exact total_ouvert)
  -- (λ a s has hs ih h, by rw bInter_insert; exact
    -- is_open_inter (h a (mem_insert _ _)) (ih (λ i hi, h i (mem_insert_of_mem _ hi))))
--end


--lemma is_open_sInter {s : set (set X)} (hs : finite s) : (∀t ∈ s, ouvert t) → ouvert (⋂₀ s) :=




lemma vide_ouvert : ouvert (∅ : set X) :=
begin
  intros x x_in,
  exfalso,
  exact x_in,
end

lemma vide_ouvert' : ouvert (∅ : set X) :=
assume x x_in, false.elim x_in


/-- L'intérieur d'une partie de X est la réunion des ouverts qu'elle contient -/
def Int (E : set X) := let I := {O : set X | ouvert O ∧ O ⊆ E} in ⋃₀ I

/-- Caractérisation métrique de l'inétrieur -/
lemma interieur_metrique (E : set X) : Int E = { x : X | ∃ r>0, boule x r ⊆ E } :=
begin
  -- Nous raisonnons par doublue inclusion
  rw le_antisymm_iff, split,  -- comment avoir la bonne notation pour l'inclusion ?
  -- Soit x dans l'intérieur de E
  intros x x_dans_Int, simp,
  -- Par définition de l'intérieur, il existe un ouvert O inclus dans E et contenant x
  rcases x_dans_Int with ⟨O, ⟨ouvert_O,O_sub_E⟩ , x_app_O⟩,
  -- L'ouvert O contient une boule autour de x
  obtain ⟨r,r_pos,boule_dans_O⟩ : ∃ r>0, boule x r ⊆ O, from ouvert_O x x_app_O,
  -- Cette boule convient 
  use [r, r_pos],
  -- puisqu'elle est incluse dans O qui est inclus dans E
  transitivity O, assumption, assumption,
  -- Pour l'autre sens, soit x le centre d'une boule incluse dans E.
  rintros x ⟨ r,r_pos, boule_dans_E⟩,
  -- Cette boule est un ouvert
  have ouvert_boule, from boule_est_ouverte x r r_pos,
  -- elle est donc incluse dans l'intérieur de E
  let I := {O : set X | ouvert O ∧ O ⊆ E},
  have boule_mem_I : (boule x r) ∈ I,
    exact and.intro ouvert_boule boule_dans_E,
  have boule_inc_Int : boule x r ⊆ Int E, from subset_sUnion_of_mem boule_mem_I,
  -- qui contient donc x, centre d'une boule incluse dans Int E
  exact boule_inc_Int (centre_mem_boule x r r_pos),
end

#print set.sUnion

example (P: X → Prop) (A : set X) (h: A = {x : X | P x}) : x ∈ A ↔ P x :=
begin
  apply iff_of_eq,
  exact congr_arg (has_mem.mem x) h,
  --exact iff_of_eq (congr_arg (has_mem.mem x) h),
end



-- Voisinages ?

end fondements



------------------------------------------------
section continuite
variables {X Y : Type} [espace_metrique X] [espace_metrique Y]

-- dans la définition suivante les `d_[X]` et `d_[Y]` sont cosmétiques, `d` seul marche aussi bien

def continue_en (f : X → Y) (x₀ : X) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x x₀ < δ → d_[Y] (f x) (f x₀) < ε   

def continue (f:X → Y) := 
∀ x : X, continue_en f x

-- Notations f continue, f continue_au_point x

-- caractérisation topologique (ponctuelle, globale)
lemma continuite_ouverts (f:X → Y): continue f ↔ ( ∀O, ouvert O → ouvert (f ⁻¹' O) ) :=
begin
  -- On raisonne par double inclusion
  split,
  { -- Supposons donc que f vérifie la définition métrique de la continuité
    -- Soit O un ouvert à l'arrivé, il s'agit de voir que son image réciproque est ouverte
    --  SOit x un point de l'image réciproque, on cherche un rayon
    intros cont O O_ouvert x x_dans_reciproque,
    -- c'est-à-dire tel que f(x) ∈ O
    simp at x_dans_reciproque,
    -- Puisque O est ouvert, il contient une boule de rayon ε autour de f(x)
    obtain ⟨ε, ε_positif, boule_dans_O⟩ : ∃ ε > 0, boule (f x) ε ⊆ O,
    from O_ouvert (f x) x_dans_reciproque,
    -- L'hypothèse de continuité fournit un δ >0
    rcases (cont x) ε ε_positif with ⟨δ , δ_positif, H⟩,
    -- Montrons que la boule de rayon δ est dans l'image réciproque
    use [δ, δ_positif],
    -- pour ceci on prend un point x' dans la boule
    intros x' hx',
    -- il s'agit de voir que son image est dans O
    simp,
    simp [boule] at hx',
    rw sym x x' at hx',
    -- La propriété de δ donnée par la continuité s'écrit d (f(x'), f(x)) < ε
    have hfx', from H x' hx',
    -- Or il suffit de voir que f(x') est dans la boule de centre f(x) et de rayon ε, 
    -- puisqu'elle est incluse dans O
    suffices hh : f x' ∈ boule (f x) ε, from boule_dans_O hh,
    -- ce qui revient à l'inégalité obtenue
    simp [boule],
    have symetrie : d_[Y] (f x') (f x) = d_[Y] (f x) (f x'), from sym (f x') (f x),
    rw symetrie at hfx', 
    assumption},
    {-- Pour l'autre direction, on suppose que l'image réciproque de tout ouvert est un ouvert,
    -- on prend un point x et un ε > 0
    rintros H x ε ε_positif,
    -- La boule de centre x et de rayon epsilon est un ouvert de Y,
    have boule_ouverte, from boule_est_ouverte (f x) ε ε_positif,
    -- donc par hypothèse son image réciproque est un ouvert de X
    have reciproque_ouvert, from H (boule (f x) ε) boule_ouverte,
      -- or x appartient à cette image réciproque
    have x_dans_reciproque: x ∈ f ⁻¹' boule (f x) ε,
      simp, simp [boule],
      rw dist_x_x_eq_zero (f x), assumption,
    -- Il existe donc une boule autour de x incluse dans l'image réciproque de la première boule
    obtain ⟨δ, δ_positif, H⟩: ∃ δ >0, boule x δ ⊆ f ⁻¹' boule (f x) ε ,  from reciproque_ouvert x x_dans_reciproque,
    -- montrons que le rayon de cette boule satisfait la définition métrique de la continuité
    use [δ , δ_positif],
    -- On considère donc un point x' tel que d(x,x') < δ
    intros x' hx',
    have symetrie : d_[X] x' x = d_[X] x x', from  sym x' x,
    rw symetrie at hx',
    -- Autrement dit, x' est dans la boule B(x,δ),
    have x'_boule : x' ∈ boule x δ, from hx',
    -- donc son image est dans la première boule
    have fx'_boule : d_[Y] (f x) (f x') < ε, from H x'_boule,
    -- ce qu'on voulait
    have symetrie_y : d_[Y] (f x) (f x') = d_[Y] (f x') (f x), from  sym (f x) (f x'),
    rw symetrie_y at fx'_boule,
    assumption},
end

-- composition (ponctuelle, globale)

def lipschitzienne (k:ℝ) (f: X → Y) := 
∀ x₀  x₁ , d_[Y] (f x₀) (f x₁) ≤ ( k * d_[X] x₀  x₁ )

-- lipschitzien implique continu


end continuite


----------------------------------------------------
section fermes
variables {X:Type} [espace_metrique X]

def ferme (F : set X) := ouvert (- F) 

-- intersection, union

-- adhérence








end fermes


----------------------------------------------------
section suites
variables {X:Type} [espace_metrique X]






end suites




