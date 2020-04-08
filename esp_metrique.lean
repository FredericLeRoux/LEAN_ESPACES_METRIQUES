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

@[simp]
lemma dist_sym (x:X) (y:X) : d x y = d y x := sym x y

@[simp]
lemma dist_x_x_eq_zero  (x:X) : d x x = 0 := 
 (sep x x).2 rfl 

lemma dist_str_pos  {x:X} {y:X} : x ≠ y → d x y > 0 := 
begin
contrapose!,
intro d_neg,
have d_pos : d x y ≥ 0, from dist_pos x y,
have d_zero : d x y = 0, from antisymm d_neg d_pos,
exact iff.mp (sep x y) d_zero
end


/-- `boule x r` est la boule ouverte de centre `x` et de rayon `r` -/
def boule (x : X) (r : ℝ)  := {y | dist x y < r}

/-- appartenir à une boule équivaut à une inégalité -/
@[simp]
lemma mem_boule (x : X) (r : ℝ) (y : X) : y ∈ boule x r ↔ dist x y < r := 
iff.rfl

/-- Une boule de rayon >0 contient son centre --/
lemma centre_mem_boule (x : X) (r : ℝ) : r > 0 → x ∈ boule x r :=
begin
intro r_pos,
simpa [boule] -- simplifie et utilise l'hypothèse
end


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
  set ε := r - d x y with hε,
  use  ε, -- le rayon candidat
  -- OBSOLETE rw exists_prop,
  split,
  { -- La ligne suivante peut être remplacée par n'importe laquelle des trois lignes qui la suivent
    simp [boule] at y_in,
    --change d x y < r at y_in,
    --rw mem_boule at y_in,
    --unfold boule at y_in, rw set.mem_set_of_eq at y_in,
    linarith only [hε, y_in]}, -- le rayon est bien strictement positif
  { -- La ligne suivante est optionnelle, elle sert  à expliciter le but
    -- change ∀ z, z ∈ boule y (r - d x y) → z ∈ boule x r,
    intros z z_in,
    rw mem_boule at *,
    have clef : d x z ≤ d x y + d y z, from triangle x y z,
    linarith only [clef, z_in, y_in, hε]} -- et l'inégalité triangulaire permet de montrer l'inclusion des boules
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
  -- OBSOLETE rw exists_prop,
  -- Il est bien positif
  split, 
    by exact lt_min r₁_pos r₂_pos,
  -- les quatre lignes qui précèdent peuvent être remplacées par :
  -- use [min r₁ r₂,lt_min r₁_pos r₂_pos]

  -- Prenons un y dans la boule de rayon r
  intros y y_app_boule, 
  -- vu le choix de r, on a d x y < r₁ et d x y < r₂
  simp [boule] at y_app_boule,
  -- donc c'est bon
  split  ; tautology
  -- FIN plus compliquée : 
  -- simp [boule] at y_app_boule,
  -- rcases y_app_boule with ⟨ineg_1,ineg_2⟩,
  -- -- il est dans O₁ et dans O₂ 
  -- have y_O₁ : y ∈ O₁, from boule_dans_O₁ ineg_1,
  -- have y_O₂ : y ∈ O₂, from boule_dans_O₂ ineg_2,
  -- -- donc dans l'intersection, comme voulu.
  -- exact and.intro y_O₁ y_O₂,
end


/-- L'espace total est ouvert -/
lemma total_ouvert : ouvert (univ : set X) :=
begin
  intros x hx,  
  use 1,
  -- OBSOLETE rw exists_prop,
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
def Int (E : set X) := ⋃₀ {O : set X | ouvert O ∧ O ⊆ E}

/-- Caractérisation métrique de l'intérieur -/
@[simp]
lemma interieur_metrique {E : set X} {x : X} : x ∈ Int E ↔  ∃ r>0, boule x r ⊆ E  :=
begin
split,
  -- Pour le sens direct, supposons que x est dans l'intérieur de E
  intro x_dans_Int, 
    -- Par définition de l'intérieur, il existe un ouvert O inclus dans E et contenant x
  rcases x_dans_Int with ⟨O, ⟨ouvert_O,O_sub_E⟩ , x_app_O⟩,
  -- L'ouvert O contient une boule autour de x
  obtain ⟨r,r_pos,boule_dans_O⟩ : ∃ r>0, boule x r ⊆ O, from ouvert_O x x_app_O,
  -- Cette boule convient 
  use [r, r_pos],
  -- puisqu'elle est incluse dans O qui est inclus dans E
  transitivity O, assumption, assumption,
  -- VARIANTE : exact subset.trans boule_dans_O O_sub_E, -- On peut aussi écrire : tauto,
  -- Pour l'autre sens, soit x le centre d'une boule incluse dans E.
rintros ⟨ r,r_pos, boule_dans_E⟩,
  -- Cette boule est un ouvert
  have ouvert_boule, from boule_est_ouverte x r r_pos,
  -- et elle contient x
  have x_mem_boule, from centre_mem_boule x r r_pos,
  -- donc x est dans l'intérieur de E
  use boule x r,
  repeat { split }, assumption, assumption, assumption,
  -- VARIANTE FIN PLUS COMPLIQUEE : -- la boule est donc incluse dans l'intérieur de E
  -- let I := {O : set X | ouvert O ∧ O ⊆ E},
  -- have boule_mem_I : (boule x r) ∈ I,
  --   exact and.intro ouvert_boule boule_dans_E,
  -- have boule_inc_Int : boule x r ⊆ Int E, from subset_sUnion_of_mem boule_mem_I,
  -- -- qui contient donc x, centre d'une boule incluse dans Int E
  -- exact boule_inc_Int (centre_mem_boule x r r_pos),
end

-- Variante moins pratique (?)
lemma interieur_metrique' {E : set X} : Int E = { x : X | ∃ r>0, boule x r ⊆ E } :=
begin
  -- Nous raisonnons par double inclusion
  apply subset.antisymm,
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
  -- VARIANTE : exact subset.trans boule_dans_O O_sub_E, -- On peut aussi écrire : tauto,
  -- Pour l'autre sens, soit x le centre d'une boule incluse dans E.
  rintros x ⟨ r,r_pos, boule_dans_E⟩,
  -- Cette boule est un ouvert
  have ouvert_boule, from boule_est_ouverte x r r_pos,
  -- et elle contient x
  have x_mem_boule, from centre_mem_boule x r r_pos,
  -- donc x est dans l'intérieur de E
  use boule x r,
  repeat { split }, assumption, assumption, assumption,
  -- VARIANTE FIN PLUS COMPLIQUEE : -- la boule est donc incluse dans l'intérieur de E
  -- let I := {O : set X | ouvert O ∧ O ⊆ E},
  -- have boule_mem_I : (boule x r) ∈ I,
  --   exact and.intro ouvert_boule boule_dans_E,
  -- have boule_inc_Int : boule x r ⊆ Int E, from subset_sUnion_of_mem boule_mem_I,
  -- -- qui contient donc x, centre d'une boule incluse dans Int E
  -- exact boule_inc_Int (centre_mem_boule x r r_pos),
end



def est_voisinage (V : set X) (x : X) := x ∈ Int V

-- caractérisation d'un voisinage en termes d'ouverts ?
-- caractérisation en terme de boules ?


end fondements



----------------------------------------------------
section continuite
----------------------------------------------------
variables {X Y : Type} [espace_metrique X] [espace_metrique Y]

-- dans la définition suivante les `d_[X]` et `d_[Y]` sont cosmétiques, `d` seul marche aussi bien

def continue_en (f : X → Y) (x₀ : X) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x₀ x < δ → d_[Y] (f x₀) (f x) < ε   

def continue (f:X → Y) := 
∀ x : X, continue_en f x

-- Notations f continue, f continue_au_point x

-- caractérisation topologique (ponctuelle, globale)
lemma continuite_ouverts (f:X → Y): continue f ↔ ( ∀O, ouvert O → ouvert (f ⁻¹' O) ) :=
begin
  -- On raisonne par double implication
  split,
  { -- Supposons donc que f vérifie la définition métrique de la continuité
    -- Soit O un ouvert à l'arrivé, il s'agit de voir que son image réciproque est ouverte
    --  SOit x un point de l'image réciproque, on cherche un rayon
    intros cont O O_ouvert x x_dans_reciproque,
    -- c'est-à-dire tel que f(x) ∈ O
    change f x ∈ O at x_dans_reciproque, -- Cette ligne est purement psychologique, on peut la retirer
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
    change f x' ∈ O, -- encore une ligne purement psychologique, Lean n'en a pas besoin
    -- Pour cela il suffit de voir que f(x') est dans la boule de centre f(x) et de rayon ε, 
    -- puisqu'elle est incluse dans O
    suffices hh : f x' ∈ boule (f x) ε, from boule_dans_O hh,
    -- ce qui est donné par la propriété de δ issue de la continuité
    exact H x' hx'
     },
  { -- Pour l'autre direction, on suppose que l'image réciproque de tout ouvert est un ouvert,
    -- on prend un point x et un ε > 0
    rintros H x ε ε_positif,
    -- La boule de centre x et de rayon epsilon est un ouvert de Y,
    have boule_ouverte, from boule_est_ouverte (f x) ε ε_positif,
    -- donc par hypothèse son image réciproque est un ouvert de X
    have reciproque_ouvert, from H (boule (f x) ε) boule_ouverte,
      -- or x appartient à cette image réciproque
    have x_dans_reciproque: x ∈ f ⁻¹' boule (f x) ε,
      simpa [boule],
    -- Il existe donc une boule autour de x incluse dans l'image réciproque de la première boule
    obtain ⟨δ, δ_positif, H⟩: ∃ δ >0, boule x δ ⊆ f ⁻¹' boule (f x) ε ,  from reciproque_ouvert x x_dans_reciproque,
    -- montrons que le rayon de cette boule satisfait la définition métrique de la continuité
    use [δ , δ_positif],
    -- On considère donc un point x' tel que d(x,x') < δ
    intros x' hx',
    -- Autrement dit, x' est dans la boule B(x,δ),
    change x' ∈ boule x δ at hx', -- encore une ligne pour rien    
    -- donc son image est dans la première boule
    exact H hx' }
end

variables {Z : Type} [espace_metrique Z]

/-- La composée de deux applications continues est continue-/
lemma composition_continue (f : X → Y) (g : Y → Z) : (continue f) →  (continue g) →  continue (g ∘ f) :=
begin
-- Supposons que f et g sont continues
intros f_cont g_cont, 
-- Nous allons utiliser la caractérisation topologique pour montrer la continuité de g ∘ f :
rw continuite_ouverts,
-- On considère un ouvert O de Z
intros O O_ouvert,
-- La caractérisation topologique de la continuité de g nous dit que g ⁻¹' O est un ouvert de Y,
have ouvert1 : ouvert (g ⁻¹' O), 
  from (((iff.elim_left (continuite_ouverts g)) g_cont) O) O_ouvert,
-- La caractérisation topologique de la continuité de f nous dit que f ⁻¹' (g ⁻¹' O) est un ouvert de X,
exact (((iff.elim_left (continuite_ouverts f)) f_cont) (g ⁻¹' O)) ouvert1,
-- et il est égal à (g ∘ f)  ⁻¹' O, CQFD
end

-- A FAIRE : caractérisation topologique de la continuité ponctuelle par les voisinages, 
-- et composition ponctuelle

def lipschitzienne (k:ℝ) (f: X → Y) := 
∀ x₀  x₁ , d_[Y] (f x₀) (f x₁) ≤ ( k * d_[X] x₀  x₁ )

-- A FAIRE : lipschitzien implique continu

end continuite


----------------------------------------------------
section fermes
----------------------------------------------------
variables {X:Type} [espace_metrique X]

def ferme (F : set X) := ouvert (- F) 

-- A FAIRE : intersection, union

/-- L'adhérence d'une partie de X est l'intersection des fermés qui la contienne -/
def Adh (E : set X) := sInter {F : set X | ferme F ∧ E ⊆ F}



-- adhérence et intérieur par passage au complémentaire

/-- Caractérisation métrique de l'adhérence -/

@[simp]
lemma adherence_metrique {E : set X} {x : X} : x ∈ Adh E  ↔ ∀ r>0, boule x r ∩ E ≠ ∅ :=
begin
  sorry
end



end fermes


----------------------------------------------------
section suites
----------------------------------------------------
variables {X:Type} [espace_metrique X]
-- variable E : set X
-- variable x : E 
-- #print x

def limite_suite (x: ℕ → X) (l : X) := ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)



-- On va voir besoin de "0<2" dans ℝ 
lemma zero_pp_2 :  (0:real) < 2 := 
begin
linarith only [zero_lt_one]
end

#print zero_pp_2 -- Waou !

open classical
local attribute [instance] prop_decidable
lemma unicite_limite {x: ℕ → X} {l₁ : X} {l₂ : X} : 
  (limite_suite x l₁) → (limite_suite x l₂) → l₁ = l₂ :=
begin
-- Supposons que la suite (x_n) converge à la fois vers l₁ et l₂ 
intros H₁ H₂,
-- Raisonnons par l'absurde, en supposant l₁ ≠ l₂ 
by_contradiction lim_non_eg,
-- Alors d(l₁, l₂) >0
have dist_limites_pos : 0 < d l₁ l₂, from dist_str_pos lim_non_eg,
-- Appelons ε la moitié de cette distance, qui est donc aussi un nombre positif
let ε := (d l₁ l₂)/2,
have ε_pos : 0 < ε, from  div_pos dist_limites_pos zero_pp_2,
-- et appliquons la définition de convergence à nos deux limites
rcases H₁ ε ε_pos with ⟨ N₁ , HN₁ ⟩,
rcases H₂ ε ε_pos with ⟨ N₂ , HN₂ ⟩,
-- On obtient deux rangs N₁, N₂, dont on prend le maximum
let N := max N₁ N₂,
-- La définition de convergence nous donne les deux inégalités d(l₁,x_N )< ε et  d(l₂,x_N) < ε
have I₁ : d l₁ (x N) < ε, from  HN₁ N (le_max_left N₁ N₂),
have I₂ : d l₂ (x N) < ε, from  HN₂ N (le_max_right N₁ N₂),
-- En les combinant à l'inégalité triangulaire entre les trois points impliqué, 
-- on obtient d(l₁,l₂) <  d(l₁,l₂), 
have egal : d l₁ l₂  = 2 * ε , from eq.symm (@mul_div_cancel' ℝ real.field (d l₁ l₂) 2 two_ne_zero),
have Ineg : d l₁ l₂ < d l₁ l₂, from
calc 
   d l₁ l₂ ≤ d l₁ (x N) + d (x N) l₂  : (triangle l₁ (x N) l₂)
    ...    ≤ d l₁ (x N) + d l₂ (x N)  : by simp
    -- Linarith se débrouille sans les 3 lignes suivante :
    -- ...    < ε + ε                    : by linarith
    -- ...    = 2 * ε                    : eq.symm (two_mul ε)
    -- ...    = d l₁ l₂                  : by rw egal, 
      ...   < d l₁ l₂                  : by linarith,
-- ce qui donne la contradiction recherchée.
linarith only [Ineg]
end

-- nom des lemmes trouvés avec la tactique library_search
example (ε : ℝ) : 2*ε = ε + ε := two_mul ε 
example (a : ℝ) (b : ℝ) (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a/b := div_pos h₁ h₂
example (a : ℝ) (b : ℝ) (H : a ≠ 0) : a * (b/a) = b := mul_div_cancel' b H
example (a : ℝ) (b : ℝ) (h₁ : a = b) : b = a := eq.symm h₁
example (a : ℝ) (h₁ : a < a) : false := by linarith
example : @has_lt.lt real real.has_lt 0 1 := zero_lt_one

-- Variante utilisant le lemme suivant :
lemma pp_que_tout_pos (l : real) : (∀ ε>0, l ≤ ε)  → l ≤ 0 :=
begin
  contrapose!,
  intro H,
  use l/2,
  split,
  linarith,
  linarith
end

lemma unicite_limite' {x: ℕ → X} {l₁ : X} {l₂ : X} : 
  (limite_suite x l₁) → (limite_suite x l₂) → l₁ = l₂ :=
begin
  intros H1 H2,
  have H : (∀ ε>0, d l₁ l₂ ≤ ε),
      intros ε ε_pos,
      have εs2_pos : ε/2>0, by linarith,
      have H1', from H1 _ εs2_pos,
      cases H1' with N₁ PN₁ ,
      have H2', from H2 _ εs2_pos,
      cases H2' with N₂ PN₂,
      have HN₁  : max N₁ N₂ ≥ N₁ , by exact le_max_left N₁ N₂, -- library_search
      have HN₂  : max N₁ N₂ ≥ N₂ , by exact le_max_right N₁ N₂, -- library_search
      specialize PN₁  _ HN₁ ,
      specialize PN₂  _ HN₂ ,
      have T, from triangle l₁ (x (max N₁ N₂)) l₂,
      have Dsym, from sym l₂ (x (max N₁ N₂)),
      exact calc 
        d l₁ l₂ ≤ d l₁ (x (max N₁ N₂)) + d (x (max N₁ N₂)) l₂ : T
          ...   ≤ ε : by linarith,
  have D , from  pp_que_tout_pos (d l₁ l₂) H,   -- : (d l₁ l₂) ≤ 0
  have D' , from dist_pos l₁ l₂,
  have D'' , by exact le_antisymm D D', -- d l₁ l₂ =0
  exact (sep l₁ l₂).1 D''
end


lemma nonvide_ssi_existe_element (A : set X) : A ≠ ∅ ↔ ∃ a : X, a ∈ A :=
ne_empty_iff_nonempty

lemma essai (a : ℝ) (b : ℝ) (c : ℝ) (H1 : a > b) (H2 : b > c) : a > c := 
begin 
  transitivity b, exact H1, exact H2,
end

lemma inv_inv2 {ε : ℝ} (ε_nz : ε ≠ 0) : ε = 1 / (1 / ε) :=
begin
  have inv_ε_nz : (1/ε) ≠ 0, from one_div_ne_zero ε_nz,
  have H : ε * (1/ε) = 1, from mul_div_cancel' 1 ε_nz,
  exact (eq_div_iff_mul_eq ε 1 inv_ε_nz).2 H,
end

-- critère séquentiel d'adhérence (construire une suite)
lemma critere_sequentiel_adherence (E : set X) (l : X) : 
          l ∈ Adh E ↔ ∃ x : ℕ → X, (∀ n, x n ∈ E) ∧ (limite_suite x l) :=
begin
split,
  -- Pour le sens direct, on prend l dans l'adhérence de E
  -- et on cherche à construire une suite d'éléments de E qui converge vers l
  intros Hl,
    -- Comment éviter d'avoir à introduire cette grosse propriété intermédiaire ?
  have H1 : ∀ n : ℕ, ∃ x : X, d l x < 1/(n+1) ∧ x ∈ E, 
    intro n,
    -- have H2, from H 1/(n+1),
    -- exact adherence_metrique.mpr l Hl,
    sorry,
  -- H1 permet de définir une suite (x_n) qui va convenir  
  choose x H using H1,
  use x,
  split,
    -- La suite est bien à valeur dans E,
    exact λ n, ((H n).2),
  -- Reste à montrer qu'elle converge vers l
    intros ε ε_pos,
    have HN, from exists_nat_gt (1 / ε),
    cases HN with N HN,
    use N, intros n Hn,
    specialize H n,
    cases H with Hutile Hinutile,
    have Ineg : N < n+1, by linarith,
    have Ineg2 : ↑n+(1:ℝ)  > ↑N, by exact_mod_cast Ineg,
    have Ineg3 : ↑n+1 > 1/ε,
      begin 
        transitivity ↑N,
        exact Ineg2,
        exact HN,
      end,
    have inv_ε_pos : (1/ε)>0, from one_div_pos_of_pos ε_pos,
    have Ineg4, by exact one_div_lt_one_div_of_lt inv_ε_pos Ineg3,
    transitivity 1 / (↑n + 1:ℝ),
      exact Hutile,
    have NZ : ε ≠ 0, by linarith,
    -- have inv_inv_ε : ε = 1/(1/ε), by inv_inv2 NZ,
    
      

    sorry,
  -- Pour l'autre direction, on suppose l'existence d'une suite 
  -- d'éléments de E convergeant vers l
rintro ⟨x,H1,H2⟩,
-- On utilise la caractérisation métrique de l'adhérence
rw adherence_metrique,
rintro r Hr, 
rw limite_suite at H2,
have H, from (H2 r) Hr,
-- obtain ⟨N, H3N⟩ : ℕ  ,(∀ (n : ℕ), n ≥ N → d l (x n) < r) , from (H2 r) Hr,
cases H with N HN,
have HNN: N ≥ N, by linarith,
specialize HN N HNN,
rw← mem_boule at HN,
specialize H1 N,
rw ne_empty_iff_nonempty,
use x N,
exact and.intro HN H1
end

example  (a : ℝ) (b : ℝ) (a_pos : a>0) (a_inf_b : a <b) : 1/a > 1/b := 
begin
  exact one_div_lt_one_div_of_lt a_pos a_inf_b
end
 
example (x : ℝ) (H : x ≠ 0) : x * (1/x) = 1 := mul_div_cancel' 1 H
example (x : ℝ) (y : ℝ) (H : x ≠ 0) : ( y = 1/x ) ↔ ( y * x = 1 ) := 
        eq_div_iff_mul_eq y 1 H



-- critère séquentiel de fermeture


-- critère séquentiel de continuité





end suites


----------------------------------------------------
section sous_espaces_metriques
----------------------------------------------------


----------------------------------------------------
section distances_equivalentes
----------------------------------------------------



----------------------------------------------------
section espaces_metriques_produits
----------------------------------------------------

----------------------------------------------------
section espaces_de_fonctions
----------------------------------------------------
