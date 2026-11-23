module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtLevel

def underT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal} :=
  ⟨P.1.under (𝓞 X.F), by
    show algebraMap (𝓞 X.F) (𝓞 X.E) _ ∈ P.1.asIdeal
    rw [map_natCast]
    exact T_mem_vT hPr u P⟩

theorem underT_bijective {Z : Dat} (hX : Z.X.Ok) (hPr : Z.Pr.Ok) (u : Z.Pr.Word) : Function.Bijective (underT hPr u) := by
  constructor
  · intro P Q h
    have h1 : P.1.asIdeal.under (𝓞 Z.X.F) = Q.1.asIdeal.under (𝓞 Z.X.F) :=
      congrArg (fun v => v.1.asIdeal) h
    rcases GlobalTheory.CharVal.eq_or_eq_conjP hX (GlobalTheory.CharVal.splitOver_vT hX hPr u Q.2).ne h1 with e | e
    · exact Subtype.ext e
    · refine absurd ?_ (conj_piT_notMem hPr u Q)
      have := decoFin_mem_of_mem_divs P.2
      rw [e, mem_conjP] at this
      exact this
  · rintro ⟨v, hv⟩
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Z.X.E) v.asIdeal
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ Q := by
      rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast] at hv
      exact hv
    have hne : Q ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hT
      exact (hPr.T_prime u).ne_zero (by exact_mod_cast hT)
    let P : HeightOneSpectrum (𝓞 Z.X.E) := ⟨Q, hQ.isPrime, hne⟩
    rw [← hPr.piT_norm u] at hT
    rcases hQ.isPrime.mem_or_mem hT with h | h
    · exact ⟨⟨P, (mem_divs (hPr.piT_ne_zero u) P).2 h⟩, Subtype.ext (HeightOneSpectrum.ext hQv.over.symm)⟩
    · exact ⟨⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP P _).2 h)⟩,
        Subtype.ext (HeightOneSpectrum.ext ((GlobalTheory.CharVal.under_conjP hX P).trans hQv.over.symm))⟩

theorem seenBar_of_not {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (hs : ¬ seenC Pr u w) (τ : X.Tau) :
    X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  rw [← map_natCast (X.embO τ), ← hPr.piT_norm u, map_mul] at hw
  refine (w.isPrime.mem_or_mem hw).resolve_left fun h => hs fun τ' => ?_
  rw [show X.embO τ' (Pr.piT u) = X.embO τ (Pr.piT u) from RingOfIntegers.ext (hPr.piT_Kq u _ _)]
  exact h

theorem mk_surj {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : Function.Surjective (Ideal.Quotient.mk P.asIdeal) :=
  Ideal.Quotient.mk_surjective

theorem mk_zero {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ P.asIdeal ↔ Ideal.Quotient.mk P.asIdeal x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.symm



def atTTied {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    AtTTied (D := (I.rec7 l Z)) u where
  eV := Equiv.ofBijective (underT l.pr u)
    (underT_bijective (Z := B.dat X I.Ch) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u)
  piU := X.piT u
  piU_K := X.piT_K u
  piU_norm := X.piT_norm u
  piU_cong := Ideal.mem_span_singleton.2 (X.piT_cong u)
  res := I.resT l u I.mu0
  res_surj v := mk_surj (X := B.fields) v.1
  res_pi v := (mk_zero (X := B.fields) v.1 _).1 (decoFin_mem_of_mem_divs (A := 𝓞 B.fields.E) v.2)
  res_conj v pb h e := by
    have h1 : pb = B.fields.conjO (X.piT u) := RingOfIntegers.ext (h.trans (B.fields_conjO_coe _).symm)
    exact conj_piT_notMem l.pr u v (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 e)
  res_v v x := mk_zero (X := B.fields) v.1 _
  tauOf w hw v x := by
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    exact (tauAt_mem_iff l.pr u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hw' v x).symm.trans
      (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).symm
  seenP w hw τ := by
    classical
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    have hs : (((I.rec7 l Z).fm u).seenP w = true) ↔ seenC (B.primes X) u w := decide_eq_true_iff
    by_cases h : seenC (B.primes X) u w
    · rw [if_pos (hs.2 h)]
      exact (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (h τ)
    · rw [if_neg (mt hs.1 h)]
      have h2 := (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (seenBar_of_not l.pr u hw' h τ)
      have h3 : ((B.fields.embO τ (B.fields.conjO (X.piT u)) : 𝓞 B.LL) : B.LL) = B.fields.emb τ (B.host.conj (X.piT u : B.host.E)) :=
        congrArg (B.fields.emb τ) (B.fields_conjO_coe _)
      exact h3 ▸ h2

theorem exists_atTTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ u : B.Word, ∃ A : AtTTied (D := (I.rec7 l Z)) u, I.IdV l u I.mu0 A.eV ∧ A.piU = X.piT u ∧ A.res = I.resT l u I.mu0 :=
  fun I _ _ l Z u => ⟨atTTied I l Z u, fun _ => rfl, rfl, by unfold atTTied; rfl⟩

end GlobalTheory.Mem.AtLevel

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LevTwist

section Re

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  have e : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id :=
    LinearMap.ext fun x => funext fun i => rfl
  rw [reL, e, Submodule.map_id]

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  rfl




theorem fun_transport {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (hL : Lb' = reL h Lb) (v : HeightOneSpectrum (𝓞 F)) {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (f' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J' Lb')) →ₗ[intV E v] M) :
    ∃ f : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) →ₗ[intV E v] M,
      (f' ≠ 0 → f ≠ 0) ∧ (∀ r : intV E v, (∀ x, f' (r • x) = 0) → ∀ x, f (r • x) = 0) ∧
      ((∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb' → f' x = 0) →
        ∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → f x = 0) ∧
      ∀ (U : Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F))) (U' : Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F))),
        U' = U.map (reGL h _).toMonoidHom → U' = levelVL σ J' v Lb' ⊓ stabFun _ f' →
        U = levelVL σ J v Lb ⊓ stabFun _ f := by
  subst h
  obtain rfl : J' = J := by
    rw [hJ]; ext i j; rfl
  obtain rfl : Lb' = Lb := by rw [hL, reL_rfl]
  refine ⟨f', id, fun _ h => h, id, ?_⟩
  rintro U U' rfl h
  rw [← h]
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · intro hg
    exact ⟨g, hg, reGL_rfl _ g⟩
  · rintro ⟨g', hg', e⟩
    have : g' = g := (reGL_rfl _ g').symm.trans e
    exact this ▸ hg'

end Re

section Pi

theorem smul_eq_zero_of_prime_card {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card M = p) (a : S) {m₀ : M} (h1 : m₀ ≠ 0) (h2 : a • m₀ = 0) (m : M) : a • m = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc h1 (g' := m))
  rw [smul_comm, h2, smul_zero]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pi_kills {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe) (v : (D.mem u).A.vT)
    (a : intV D.host.E (A.eV v).1)
    (ha : (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) =
      inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU : 𝓞 D.host.E) : D.host.E))
    (m : K.lev.fM (A.eV v).1 (A.eV v).2) : a • m = 0 := by
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨x, hx⟩ : ∃ x, (D.fm u).fv i v c x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact (D.fm u).fv_ne i v c (LinearMap.ext hc)
  obtain ⟨z, rfl⟩ := P.pr_surj v c x
  have hin : ∀ z : ↥(Ld D u i hi c), ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
    fun z => (GlobalTheory.LevelHecke.MovePair.ld_loc K _ c _).1 (Submodule.subset_span ⟨z.1, z.2, rfl⟩)
  have h1 : K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ ≠ 0 := by
    intro h0
    apply hx
    rw [hT v c z (hin z), h0, map_zero]
  have h3 : K.lev.fT _ (A.eV v).2 ⟨_, hin (A.piU • z)⟩ = 0 := by
    have hz0 : (D.fm u).fv i v c (P.pr v c (A.piU • z)) = 0 := by
      rw [P.pr_smul, A.res_pi, zero_smul, map_zero]
    exact (fMe v).injective (((hT v c _ (hin _)).symm.trans hz0).trans (map_zero (fMe v)).symm)
  have e : a • (⟨_, hin z⟩ : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))) =
      ⟨_, hin (A.piU • z)⟩ := by
    apply Subtype.ext
    have e1 : (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b)) =
        (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
          fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b) := by
      funext b
      rw [ha]
      show inclE (F := D.host.F) _ (((A.piU : 𝓞 D.host.E) : D.host.E) * z.1 b) = _
      rw [map_mul]
      rfl
    show (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
        (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b))) =
        ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b))
    rw [e1, Matrix.mulVec_smul]
  have h2 : a • K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ = 0 :=
    (map_smul (K.lev.fT _ (A.eV v).2) a _).symm.trans ((congrArg (K.lev.fT _ (A.eV v).2) e).trans h3)
  exact smul_eq_zero_of_prime_card (D.mem u).A.T_prime (K.lev.fM_card _ _) a h1 h2 m

end Pi

section Main




theorem stepZeroHermitianLevel_with_formsFunctional (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (hS : SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)) :
    ∃ L' : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
        (a : intV D.host.E w),
        (a : TensorProduct D.host.F D.host.E (w.adicCompletion D.host.F)) =
          inclE (F := D.host.F) (w.adicCompletion D.host.F) ((F.atT.piU : 𝓞 D.host.E) : D.host.E) →
        ∀ m : L'.fM w h, a • m = 0 := by
  have hJ : gramN D 0 (Nat.zero_le _) =
      (D.sp.gram0).reindex (finCongr (rank_eq_first_level D.R)) (finCongr (rank_eq_first_level D.R)) := by
    ext i j
    rfl
  have key := fun (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal) =>
    fun_transport (rank_eq_first_level D.R) (sigD D) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) hJ L.Lb
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hS.Lb_eq w
      ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT w h)
  choose fT' k1 k2 k3 k4 using key
  refine ⟨{ L with
    fM := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM
    fM_acg := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_acg
    fM_mod := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_mod
    fT := fT'
    fT_ne := fun v h => k1 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne v h)
    fT_T := fun v h => k2 v h _ ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_T v h)
    fM_card := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card
    fT_L := fun v h => k3 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L v h)
    UlocAlt := fun v h => k4 v h _ _ (hS.Uloc_eq v) ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.UlocAlt v h) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w h a ha m
  obtain ⟨v, hv⟩ := F.atT.eV.surjective ⟨w, h⟩
  have hw : (F.atT.eV v).1 = w := congrArg Subtype.val hv
  subst hw
  exact pi_kills (F.lv 0 (Nat.zero_le _)) (F.cls 0 (Nat.zero_le _) (Or.inl rfl))
    (F.fMe 0 (Nat.zero_le _) (Or.inl rfl)) (F.fv 0 (Nat.zero_le _) (Or.inl rfl)) v a ha m

end Main




theorem stepZeroHermitianLevel_uniformiser_kills_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 :=
  by
  intro B X I _ _ l Z u Ch chOf F _ L hS
  exact stepZeroHermitianLevel_with_formsFunctional (I.rec7 l Z) u F L hS

end GlobalTheory.Mem.Col2.LevTwist

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PtTwist

open GlobalTheory.Mem.Col2.PtExist

theorem exists_ptOf_twists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ)
    (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  classical
  intro B X I hI u n p
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨hlev, hGQ, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)

  have hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P hP => by
    have h1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 hP
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h1

  have hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ),
      ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P m => by
    rw [mem_conjP, map_natCast]

  have hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP =>
    T_notMem_vGs hPr u ⟨P, hP⟩

  have hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP h => by
    have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u
  have hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs :=
    Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)
  have hTQ : Disjoint ((B.primes X).vT u) I.SQ :=
    Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)
  have hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP => by
    rcases Finset.mem_union.1 hP with h | h
    exacts [hG P h, hQ P h]
  refine PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  ·
    have a1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 h1
    have a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := (mem_divs hT0 _).1 h2
    rw [mem_conjP] at a2
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    have : (1 : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · exact hout _ h2 ((hcj P _).2 (hTin P h1))
  · exact hout P h1 ((hcj P _).1 (hTin _ h2))
  · exact hlev.split P h1 h2

end GlobalTheory.Mem.Col2.PtTwist
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.LshOffLevel

theorem mem_divs_of' {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact (hf.mem_toFinset.1 h)
  · simp at h

theorem lsh_lattice_and_loc_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Y : DivX (I.rec7 l Z)) (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (j : ℕ), j ≤ B.R.m → ∀ (c : (I.stp u μ j).Cl), Submodule.IsLattice B.fields.E ((I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ∧ ∀ x : Fin (B.R.N j) → B.fields.E, (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c)) ↔ (∃ s : ℕ, ¬ (I.rec7 l Z).what₂.places.resChar w ∣ s ∧ (s : B.fields.E) • x ∈ ((I.stp u μ j).rep c).1.1.deco.1.N) := by
  intro B X I hOk hPins l Z Y u μ w hw j hj c
  classical
  have hpP : ((I.rec7 l Z).what₂.places.resChar w).Prime := (I.rec7 l Z).what₂.places.resChar_prime w
  have hTP : (B.T u).Prime := l.pr.T_prime u
  have hpT : ¬ (I.rec7 l Z).what₂.places.resChar w ∣ B.T u := fun h => hw.1 ((Nat.prime_dvd_prime_iff_eq hpP hTP).1 h)
  set d := ((I.stp u μ j).rep c).1.1.deco with hd
  have hE : (I.stp u μ j).Lsh c.1 ((I.stp u μ j).rep c) = d.1.Lsh := rfl
  rw [hE]
  have hTP' : ∀ P : (B.primes X).vT u, (((B.T u : ℕ) : 𝓞 B.fields.E)) ∈ (P : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    intro P
    have hpi := mem_divs_of' P.2
    rw [← l.pr.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  have hLN : ∀ x ∈ d.1.Lsh, ((B.T u : ℕ) : B.fields.E) • x ∈ d.1.N := by
    intro x hx
    have := d.2.smul_Lsh_mem_N (a := ((B.T u : ℕ) : 𝓞 B.fields.E)) (fun P => by rw [map_natCast]; exact hTP' P) hx
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul B.fields.E] at this
  refine ⟨d.2.Lsh_lattice, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨B.T u * s, fun h => (hpP.dvd_mul.1 h).elim hpT hs, ?_⟩
    have h3 := hLN _ hx
    have e : ((B.T u * s : ℕ) : B.fields.E) • x = ((B.T u : ℕ) : B.fields.E) • ((s : B.fields.E) • x) := by
      rw [smul_smul, ← Nat.cast_mul]
    exact e ▸ h3
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, d.2.N_le_Lsh hx⟩

end GlobalTheory.LshOffLevel
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

def ssRep {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k :=
  Classical.epsilon fun ρ' : Γ →* GL (Fin a) k => IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
    ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly

def BcGood (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) ∧
  rankIso D.nd D.naut Sig = D.R.r ∧ ∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = Rw.locR σ w


open Classical in
def bcOf (D : D7) (Rw : RowSide D) (σ : D.what₂.FT) : Multiset (ℕ × ℕ) :=
  if h : ∃ Sig, BcGood D Rw σ Sig then Multiset.ofList (h.choose.map fun p => (p.a, p.d)) else {(D.R.r, 1)}

def RbarData {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) : Prop :=
  ∃ i : X.nd.Loc, X.nd.w i = lam ∧ ∃ (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)),
    HasParamW X.nd Y.naut i σ Sig ∧ IsRepOfSig X.nd Y.naut i Sig ρ


open Classical in
def rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    G D.host.E X.nd.Om →* GL (Fin D.R.r) (Fb (D.what₂.places.resChar lam) (D.what₂.places.resChar_prime lam)) :=
  if h : RbarData Y σ lam then
    ssRep (mapRep (((fbCast (h.choose_spec.1 ▸ X.nd.w_l h.choose).symm (X.nd.lPrime h.choose).out
        (D.what₂.places.resChar_prime lam)).toRingHom.comp
      ((Y.naut.kFbar h.choose).comp (IsLocalRing.residue (X.nd.O h.choose))))) h.choose_spec.2.choose_spec.choose)
  else 1

def mtSup {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (i : X.nd.Loc) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i)) :=
  ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧
      IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P

def castMt {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j)) :
    Submodule ℂ (D.what₂.Mt μ' j') := by
  subst h1; subst h2; exact M


open Classical in
def mtParOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (μ : D.what₂.Tup) (j : ℕ) (σ' : (lay0 D).ntypes.Par) :
    Submodule ℂ (D.what₂.Mt μ j) :=
  if h : ∃ i, X.nd.mu i = μ ∧ X.nd.j i = j then castMt h.choose_spec.1 h.choose_spec.2 (mtSup Y h.choose σ') else ⊥

end GlobalTheory.HeightCounting

end
end
