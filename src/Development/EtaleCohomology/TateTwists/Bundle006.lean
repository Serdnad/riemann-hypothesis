module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.TateTwists.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf : Prop :=
  ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition : Prop :=
  ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTateTwistSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorAcyclicOfFlatBounded : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x)) → ∃ φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧ ∀ U x, φ U (τ.lift U w x) = b U x
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T T3 : Cx R} (τ : Pair I J T) (τ' : Pair T K T3), τ.IsTensor → τ'.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L), ∃ ν : Pair T K L, ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy : Prop :=
  ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧ ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensLocbij

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P)
    (h2 : Loc U Q) : Loc U (fun V g => P V g ∧ Q V g) := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem map_comp_apply' (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    {U V W : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (p : P.obj (op U)) :
    (P.map (k ≫ g).op).hom p = (P.map k.op).hom ((P.map g.op).hom p) := by
  simp [op_comp, Functor.map_comp]

end LateralTheory.EtaleFoundations.TensLocbij
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def twpair_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor

def twpair_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def twpair_tens_twres : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def twpair_twres_ext : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

def twpair_cup_compat : Prop :=
  ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b)

def twpair_zc_fun : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n)

theorem etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties (h1 : twpair_tens_ex) (h2 : twpair_tens_univ) (h3 : twpair_tens_twres)
    (h4 : twpair_twres_ext) (h5 : twpair_cup_compat) (h6 : twpair_zc_fun) : LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  have hT := h3 q i j (i + j) rfl _ _ (h4 q i).1 (h4 q j).1 (h4 q j).2.1 τ hτ
  obtain ⟨⟨u, hu⟩, hhom⟩ := (h4 q (i + j)).2.2 _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := (h2 (ZMod q) τ hτ).2.2 u
    apply pick_spec
    refine ⟨ν, fun U ζ => ?_⟩
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [← hu U ζ, this]
    rfl
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := (h2 (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := (h2 (ZMod q) τ hτ).1 ν (𝟙 _) (𝟙 _)
    have hgen : ∀ U ζ, Sec.map (uμ.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) =
        Sec.map (uν.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) := by
      intro U ζ
      rw [huμ U 0 0 0 (add_zero 0), huν U 0 0 0 (add_zero 0)]
      exact (hμ U ζ).trans (hν U ζ).symm
    have hh := hhom uμ uν hgen
    have hp := ((h6 (ZMod q)).2.2.2.2 uμ uν hh ((chains (ZMod q)).obj E) w).2
    have hid := (h6 (ZMod q)).1
    ext a b
    have e1 := h5 (ZMod q) τ μ (𝟙 _) (𝟙 _) uμ huμ E h a b
    have e2 := h5 (ZMod q) τ ν (𝟙 _) (𝟙 _) uν huν E h a b
    rw [(hid _ _ n a).2, (hid _ _ m b).2] at e1 e2
    rw [← e1, ← e2, hp]

end LateralTheory.EtaleFoundations
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainExistsFromNaturalSections : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def EtaleSimplicialCochainEvaluationDifferentialFormula : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleSimplicialCochainEvaluationProperties : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ), m + 1 = n → ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, ev α.1 0 n (by simp) X (𝟙 X) = 0 → ∃ β : Cochain ((chains R).obj (sch.obj X)) I m, δ m n β = α.1

def a0 {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U
  | 0, s, h, U, x => (show n = s by omega) ▸ Sec.res (x : U ⟶ X) z
  | _ + 1, _, _, _, _ => 0

lemma etaleSimplicialCochain_scheme_section_extension_degree_zero {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) (h : -((0:ℕ) : ℤ) + n = n)
    (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) : a0 X I n z 0 n h U x = Sec.res (x : U ⟶ X) z := rfl

lemma res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res, op_comp, Functor.map_comp]

lemma res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (z : Sec F U) : Sec.res (𝟙 U) z = z := by
  simp [Sec.res]

lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => ModuleCat.Hom.hom f z) (φ.hom.naturality g.op)

lemma etaleSimplicialCochain_scheme_section_extension_naturality {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a0 X I n z p s h U x) = a0 X I n z p s h V (x.res g) := by
  intro p s h V U g x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    exact res_res g x z
  | succ q => simp [a0, Sec.res]

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) (hcob : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary) : EtaleSchemeGlobalSectionCohomologyClass := by
  intro R _ X I m n k hmn hnk

  have v0 : ∀ {q : ℤ} (β : Cochain ((chains R).obj (sch.obj X)) I q) (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
      ev β 0 q (by simp) U x = Sec.res (x : U ⟶ X) (ev β 0 q (by simp) X (𝟙 X)) := by
    intro q β U x
    rw [(hb R).2.1 β 0 q (by simp) U X x (𝟙 X)]
    rfl
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨α, hα⟩ := hmk R (a0 X I n z) (etaleSimplicialCochain_scheme_section_extension_naturality X I n z)
    have hδ : δ n k α = 0 := by
      apply (hb R).2.2.1
      intro p s h U x
      rw [((hb R).1 (δ n k α) (δ n k α) p s h U x).2.2.1]
      cases p with
      | zero =>
        obtain rfl : s = k := by omega
        rw [(hdl R hnk α U).1 x, hα, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        exact (map_res (I.d n s) (x : U ⟶ X) z).trans (by rw [hz]; simp [Sec.res])
      | succ p =>
        rw [(hdl R hnk α U).2 p (-((p + 1 : ℕ) : ℤ) + n) s rfl h x]
        simp only [hα]
        cases p with
        | zero =>
          obtain rfl : s = n := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
    refine ⟨Cocycle.mk α k hnk hδ, ?_, ?_⟩
    · intro U x; exact hα 0 n (by simp) U x
    · intro p s h U x; rw [show (Cocycle.mk α k hnk hδ).1 = α from rfl, hα]; rfl
  · intro α
    have hd0 : Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 := by
      rw [← (hdl R hnk α.1 X).1 (𝟙 X), Cocycle.δ_eq_zero]
      exact ((hb R (E := sch.obj X) (I := I) (n := k)).1 0 0 0 k (by simp) X (𝟙 X)).2.2.1
    refine ⟨hd0, ?_⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      rw [← (hdl R hmn β X).1 (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := hmk R (a0 X I m y) (etaleSimplicialCochain_scheme_section_extension_naturality X I m y)
      have hc : δ n k (α.1 - δ m n γ) = 0 := by
        rw [δ_sub, Cocycle.δ_eq_zero, δ_δ, sub_zero]
      obtain ⟨β, hβ⟩ := hcob R X I m n hmn (Cocycle.mk (α.1 - δ m n γ) k hnk hc) (by
        have e := ((hb R).1 (α : Cochain ((chains R).obj (sch.obj X)) I n) (δ m n γ) 0 n (by simp) X (𝟙 X)).2.1
        have e2 : ev (δ m n γ) 0 n (by simp) X (𝟙 X) = Sec.map (I.d m n) y := by
          rw [(hdl R hmn γ X).1 (𝟙 X)]
          exact congrArg (Sec.map (I.d m n)) ((hγ 0 m (by simp) X (𝟙 X)).trans (res_id y))
        exact e.trans ((congrArg (ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n (by simp) X (𝟙 X) - ·) e2).trans
          (sub_eq_zero.mpr hy.symm)))
      refine ⟨β + γ, ?_⟩
      rw [δ_add, hβ]
      show α.1 - δ m n γ + δ m n γ = α.1
      abel
end
