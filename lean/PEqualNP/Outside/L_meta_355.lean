import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi

theorem PEqualNP.Outside.L_meta_355 : ∀ E : List (Fin 4 × Fin 4), E = [(0, 1), (1, 2), (2, 3)] → ∀ (PV RV : Fin 2 → Finset (Fin 4)) (PG RG : Fin 2 → Finset (Fin 2)) (OV : Finset (Fin 4)) (OG : Finset (Fin 2)) (val : Finset (Fin 4) → Fin 2 → Prop), (∀ i : Fin 2, ∀ j ∈ PG i, j < i) → (∀ i : Fin 2, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin 4)) (i : Fin 2), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin 4), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X) → ∀ (g H : Fin 2) (u : Fin 4), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin 2, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin 4), (∀ e ∈ E, ¬ (e.1 ∈ I ∧ e.2 ∈ I)) → u ∉ I → (∃ w ∈ I, (u, w) ∈ E ∨ (w, u) ∈ E) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro E hE PV RV PG RG OV OG val _hPG hRG hVal hOut g H u hgH _huPV huRV _hUse I hI _huI hNeighbor hHI
  have loopFree : ∀ v : Fin 4, (v, v) ∉ E := by
    rw [hE]
    decide
  have other : ∀ a b c : Fin 2, a ≠ b → c ≠ a → c = b := by decide
  have noOutputVariables : ∀ v ∈ OV, False := by
    intro v hv
    obtain ⟨e, he, hFirst, hSecond⟩ := (hOut {v}).mp (Or.inl ⟨v, hv, by simp⟩)
    have hPair : e = (v, v) :=
      Prod.ext (Finset.mem_singleton.mp hFirst) (Finset.mem_singleton.mp hSecond)
    exact loopFree v (hPair ▸ he)
  have outputFalse : ¬ ((∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j) := by
    intro h
    obtain ⟨e, he, hp, hq⟩ := (hOut I).mp h
    exact hI e he ⟨hp, hq⟩
  have hHNotOutput : H ∉ OG := fun h => outputFalse (Or.inr ⟨H, h, hHI⟩)
  have newEdge : ∃ e ∈ E, e.1 ∈ insert u I ∧ e.2 ∈ insert u I := by
    obtain ⟨w, hw, h | h⟩ := hNeighbor
    · exact ⟨(u, w), h, Finset.mem_insert_self u I, Finset.mem_insert_of_mem hw⟩
    · exact ⟨(w, u), h, Finset.mem_insert_of_mem hw, Finset.mem_insert_self u I⟩
  obtain hVars | ⟨j, hjOut, hjTrue⟩ := (hOut (insert u I)).mpr newEdge
  · obtain ⟨v, hv, _⟩ := hVars
    exact (noOutputVariables v hv).elim
  have hj : j = g := by
    by_contra h
    exact hHNotOutput (other g H j hgH h ▸ hjOut)
  subst j
  have hNotG : ¬ val I g := fun h => outputFalse (Or.inr ⟨g, hjOut, h⟩)
  have rightFactor : (∃ v ∈ RV g, v ∈ I) ∨ ∃ k ∈ RG g, val I k := by
    rcases ((hVal (insert u I) g).mp hjTrue).2 with ⟨v, hv, hvInserted⟩ | ⟨k, hk, _⟩
    · rcases Finset.mem_insert.mp hvInserted with rfl | hvI
      · exact (huRV hv).elim
      · exact Or.inl ⟨v, hv, hvI⟩
    · have hkH := other g H k hgH (ne_of_lt (hRG g k hk))
      subst k
      exact Or.inr ⟨H, hk, hHI⟩
  have leftFalse : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ k ∈ PG g, val I k) :=
    fun h => hNotG ((hVal I g).mpr ⟨h, rightFactor⟩)
  exact ⟨fun v hv hvI => leftFalse (Or.inl ⟨v, hv, hvI⟩),
    fun k hk h => leftFalse (Or.inr ⟨k, hk, h⟩),
    fun h => leftFalse (Or.inr ⟨H, h, hHI⟩)⟩
