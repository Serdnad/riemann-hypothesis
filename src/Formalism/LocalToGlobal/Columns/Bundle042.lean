module

public import Formalism.LocalToGlobal.Columns.Bundle040
public import Formalism.LocalToGlobal.Columns.Bundle038
import Formalism.LocalToGlobal.HermitianForms.Bundle007
public import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.Bundle021
public import Formalism.LocalToGlobal.Columns.Bundle020
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Repack0

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {sp : Spaces R F E} {gp : Fin 2 → ℕ} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
  {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {bad : Set (HeightOneSpectrum (𝓞 F))}

def LevPack.toCol (P : LevPack sp.cm R.k sp.gram0 gp A.T R.f bad (C.stab 0) fun c => sp.crdLat0 (clsLat 0 c))
    (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (spl_sig : ∀ i v h x, spl i v h (sigR sp.cm.sig (v.adicCompletion F) x) = swapR _ (spl i v h x))
    (hiw : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
      ∀ x ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F), x ∈ P.lev.Uloc v ↔
        (1 : GL (Fin R.k) (v.adicCompletion F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU F R.k v)
    (w1 : HeightOneSpectrum (𝓞 F)) (reflection_mem_Glev_castSucc : (gp 0 : 𝓞 F) ∈ w1.asIdeal) :
    ColLevel R F E sp gp C A clsLat where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := P.lev.Lb_int
  Lb_dual := P.lev.Lb_dual
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_le := P.lev.Uloc_le
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  splitG := spl
  splitG_sig := spl_sig
  frG := fun _ _ _ => 1
  Uloc_g := hiw
  fM := P.lev.fM
  fT := P.lev.fT
  fT_ne := P.lev.fT_ne
  fT_T := P.lev.fT_T
  fM_card := P.lev.fM_card
  fT_L := P.lev.fT_L
  UlocAlt := P.lev.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq
  U_compact := P.lev.U_compact
  U_open := P.lev.U_open
  w1 := w1
  reflection_mem_Glev_castSucc := reflection_mem_Glev_castSucc
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := P.cls.stabI_range
  stabI_lat := P.cls.stabI_lat

end Repack0

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (spl : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g i : 𝓞 X.F) ∈ v.asIdeal →
      X.E ⊗[X.F] v.adicCompletion X.F ≃+* v.adicCompletion X.F × v.adicCompletion X.F)

def IwLoc : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
    ∀ x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (v.adicCompletion X.F), x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
      (1 : GL (Fin n) (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F n v

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

theorem levPack_iw (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (hI : IwLoc hc u Λ spl) (H : HCrd Pr n fun c => (s c).1.L) :
    ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal),
      ∀ x ∈ UPts hc.sig H.J (v.adicCompletion X.F), x ∈ (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Uloc v ↔
        (1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ * bc ((RingHom.fst _ _).comp (spl i v h).toRingHom) x * 1 ∈ iwU X.F H.n' v := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact hI

def th_resMap (P : Pl X.E) : 𝓞 X.F ⧸ (underPl X.F P).asIdeal →+* 𝓞 X.E ⧸ P.asIdeal :=
  Ideal.quotientMap P.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E)) (le_of_eq rfl)

include hPr in
theorem th_resMap_bij (P : {P // P ∈ Pr.vT u}) : Function.Bijective (th_resMap (X := X) P.1) := by
  constructor
  · exact Ideal.quotientMap_injective' (le_of_eq rfl)
  · intro b
    haveI : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    haveI : Nontrivial (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.1.isPrime.ne_top
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← Ideal.absNorm_eq_natCard]
      exact hPr.vT_norm u P.1 P.2
    obtain ⟨k, hk⟩ := mem_zmultiples_of_prime_card hcard (g := (1 : 𝓞 X.E ⧸ P.1.asIdeal)) (g' := b) one_ne_zero
    refine ⟨(k : 𝓞 X.F ⧸ (underPl X.F P.1).asIdeal), ?_⟩
    rw [map_intCast, ← hk]
    simp

def tieFv (P : {P // P ∈ Pr.vT u}) : (𝓞 X.E ⧸ P.1.asIdeal) ≃+* (𝓞 X.F ⧸ (tieEV hc hX hPr u P).1.asIdeal) :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm

theorem tieFv_mk (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    tieFv hc hX hPr u P (Ideal.Quotient.mk P.1.asIdeal (algebraMap (𝓞 X.F) (𝓞 X.E) x)) = Ideal.Quotient.mk _ x :=
  (RingEquiv.ofBijective (th_resMap (X := X) P.1) (th_resMap_bij hPr u P)).symm_apply_apply (Ideal.Quotient.mk _ x)


include hX hPr in
theorem exists_place_over_first_prime : ∃ v : HeightOneSpectrum (𝓞 X.F), (Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal := by
  have hcard : 0 < (Pr.vG 0).card := by rw [hPr.vG_card 0]; exact hX.f_pos
  obtain ⟨P, hP⟩ := Finset.card_pos.1 hcard
  refine ⟨underPl X.F P, ?_⟩
  show (Pr.g 0 : 𝓞 X.F) ∈ P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast, ← hPr.piG_norm 0]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs hP)

end Gen

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem tq_tfaZ_symm {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) (v : Sp E N) (i : Fin N) :
    (Sc.Fr.tfaExtZ hN f z hz).symm v i =
      if h : i.1 < n then f.symm (fun j : Fin n => v ⟨j.1, by omega⟩) ⟨i.1, h⟩ else z⁻¹ * v i := by
  subst hN
  show (Sc.Fr.tfaD z hz).symm ((extE f).symm v) i = _
  rw [Sc.Fr.tfaD_symm_apply]
  by_cases h : i.1 < n
  · rw [dif_pos h, if_neg (fun h' => by rw [h'] at h; simp at h)]
    obtain ⟨j, rfl⟩ : ∃ j : Fin n, i = Fin.castSucc j := ⟨⟨i.1, h⟩, Fin.ext rfl⟩
    show initL E n ((extE f).symm v) j = _
    rw [initL_extE_symm]
    rfl
  · rw [dite_eq_right h]
    obtain rfl : i = Fin.last n := Fin.ext (by have := i.2; simp; omega)
    rw [if_pos rfl, extE_symm_last]

end Gen

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks}
variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))


open Classical in

theorem xiTopTilQ_holds (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (u : Pr.Word)
    (hpi : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (p' : DecoF X.E (R.N R.m) (Pr.vT u) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (hp' : p'.deco = tilC sel mu u d)
    (hfr : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)),
      p'.fr ⟨P, hP⟩ = (Sc.Fr.topFrA (R := R) sel mu u (Finset.subset_union_left : Pr.vGs ⊆ rowSG Pr sel mu)
        (fun P hP => Finset.mem_union_right _ hP)).fr ⟨P, hP⟩ d)
    (hY : Y ∈ ybSet sel mu cst p.deco.1.N) :
    XiTopG Ch sel mu cst (m2 + 1) R.m (R.N R.m) p Y p' = XiCpl2 Ch sel mu cst m2 p Y d := by
  classical
  funext x
  unfold XiTopG XiCpl2
  have e0 : phiT X.K p.deco.1 p'.deco.1 x = phiT X.K p.deco.1 (tilQ sel mu u d).1 x := by rw [hp']; rfl
  rw [e0]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hlast : R.N R.m - 1 < R.N R.m := by have := R.N_pos R.m; omega
  by_cases hP : P.1 ∈ Pr.vGs
  · have eF : frsG sel mu p' P = (tilQ sel mu u d).1.liftFr P := by
      unfold frsG
      rw [dif_pos hP, hp']
      rfl
    have ef : frsF sel mu p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dif_pos hP]
    rw [eF]
    have hT : ∀ Q : Pr.vT u, cO X.E (Pr.piT u) ∉ Q.1.asIdeal := fun Q => conj_piT_notMem hPr u Q
    have hG : ∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal := hpi
    have hF' : (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1.IsLift P ((tilQ sel mu u d).1.liftFr P) :=
      Deco.liftFr_spec ((tilQ sel mu u d).2.hasLift P)
    have hf0 : d.1.IsLift P (d.1.liftFr P) := Deco.liftFr_spec (d.2.hasLift P)
    have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R (m2 + 1))
      (n' := R.N (m2 + 1)) (n := R.N R.m - 1) (N := R.N R.m) (xt_cOf hm) (PhiTop Ch mu cst.sharp m2 P.1)
      (fun x x' h => xtPhiTop_congr Ch mu hX hPr hm cst.sharp hP x x' h) (fun x h => xtPhiTop_int Ch mu hm cst.sharp hP x h)
      (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXp X.E R) (atNL X.E (R.N R.m) (R.N R.m - 1))
      (fun a => by
        constructor
        · intro h
          refine ⟨fun i => h _, ?_⟩
          unfold atNL
          rw [dif_pos hlast]
          exact h _
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i.1 < R.N R.m - 1
          · exact h1 ⟨i.1, by omega⟩
          · unfold atNL at h2
            rw [dif_pos hlast] at h2
            have : i = ⟨R.N R.m - 1, hlast⟩ := Fin.ext (by show i.1 = R.N R.m - 1; have := i.2; omega)
            rw [this]
            exact h2)
      (((tilQ sel mu u d).1.liftFr P).symm.toLinearMap ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      (fun j => by
        have h := xtMid (ST := Pr.vT u) (N_m_succ R) d hT hG P _ hF' _ hf0 (x (frsF sel mu p P (Pi.single j 1)))
        have el : ∀ a : Sp X.E (R.N R.m), atNL X.E (R.N R.m) (R.N R.m - 1) a = a ⟨R.N R.m - 1, hlast⟩ := fun a => by
          unfold atNL
          rw [dif_pos hlast]
          rfl
        refine ⟨?_, fun hall => ⟨fun i => ?_, ?_⟩⟩
        · refine h.1.trans (and_congr Iff.rfl ?_)
          show _ ↔ IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P (Pi.single j 1))))
          rw [el]
        · exact (h.2 hall).1 ⟨i.1, by have := i.2; omega⟩
        · show redP P.1 (atNL X.E (R.N R.m) (R.N R.m - 1) _) =
            redP P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P (Pi.single j 1))))
          rw [el, el]
          exact (h.2 hall).2)
      ((frsF sel mu p P).symm (repY Y)) (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hY P hP j)
    unfold ftY
    rw [if_pos hP, if_pos hP]
    exact key
  ·
    have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
    have hz : (algebraMap (𝓞 X.E) X.E (Pr.piT u)) ≠ 0 := fun h0 => hpi P (by
      rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0
      rw [h0]
      exact zero_mem _)
    have hOk : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal :=
      ⟨d.2.til (fun Q => conj_piT_notMem hPr u Q) hpi, hpi P⟩
    have eF : frsG sel mu p' P = Sc.Fr.tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, Finset.mem_union_right _ hPQ⟩)
        (algebraMap (𝓞 X.E) X.E (Pr.piT u)) hz := by
      unfold frsG
      rw [dite_eq_right hP, hfr P.1 hPQ]
      unfold Sc.Fr.topFrA
      simp only [dif_pos hOk]
    have hA : prXpG X.E (R.N R.m) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x =
        (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap := by
      rw [eF]
      refine LinearMap.ext fun v => funext fun i => ?_
      show (Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v)) ⟨i.1, _⟩ = _
      rw [tq_tfaZ_symm, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hB : atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x =
        (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap := by
      rw [eF]
      refine LinearMap.ext fun v => ?_
      show atNL X.E (R.N R.m) (R.N R.m - 1) ((Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v))) =
        ((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (x (frsF sel mu p P v))
      unfold atNL
      simp only [dif_pos hlast]
      show (Sc.Fr.tfaExtZ (N_m_succ R) _ _ hz).symm (x (frsF sel mu p P v)) ⟨R.N R.m - 1, hlast⟩ = _
      rw [tq_tfaZ_symm, dite_eq_right (show ¬ (R.N R.m - 1 < R.N R.m - 1) from lt_irrefl _)]
      rfl
    rw [show (prXpG X.E (R.N R.m) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
        LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
          LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) by
      rw [← LinearMap.comp_assoc, hA]
      rfl, hB]
    unfold PhiTopG PhiTop
    (try simp only [hP, if_false])

end Fin

end Formalism.L2.Col
end
end
