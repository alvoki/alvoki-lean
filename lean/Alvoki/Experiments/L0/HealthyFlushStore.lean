import Alvoki.Experiments.L0.NativeFlushStore

namespace ExperimentalL0.NativeFlushStore
open NativeRead (tableNamespace)
open NativeTableCreate (Candidate HealthyDirectory)
open NativeFlushRestart (proposal)

theorem healthyPinned (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size)
    (candidate : Candidate (root / "tables") origin)
    (rows : ImmutableSSTable.Unified.modelBuild Alvoki.CRC32C.extend (tableLayout candidate.number.toUInt64)
      (s.mem.toList.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) {} = .ok (count, bytes))
    (writer : NativeTableWriter.Healthy (tablePath (root / "tables") candidate.number.toUInt64)
      candidate.number.toUInt64 s.mem.toList candidate.reserved)
    (dir : HealthyDirectory (tableNamespace physical root) s.mem.toList candidate)
    (reports : ∀ w, NativeFlush.createTable root s.mem.toList origin = .ok candidate.number.toUInt64 w →
      NativeManifestPublish.Healthy (root / "manifest") (L0Manifest.encode (proposal image s candidate.number.toUInt64)) w
        (Ready physical root lock ref wal image s candidate.number.toUInt64 media) manifest) :
    ∃ t, NativeFlush.store root image s origin = .ok ⟨proposal image s candidate.number.toUInt64, ∅⟩ t ∧
      Ready physical root lock ref wal image s candidate.number.toUInt64 media t ∧
      (physical t).manifest.Stable (L0Manifest.encode (proposal image s candidate.number.toUInt64)) ∧
      ∃ w, NativeFlush.createTable root s.mem.toList origin = .ok candidate.number.toUInt64 w ∧
        SameFile media candidate.number.toUInt64 s.mem.toList w t := by
  obtain ⟨w, created, pre, saved⟩ := NativeTableCreate.healthy io.table TableFrame.refl (fun _ f => ⟨(start.advance f).live,(start.advance f).durable⟩)
    candidate rows writer dir
  change NativeFlush.createTable root s.mem.toList origin = _ at created
  have r : Ready physical root lock ref wal image s candidate.number.toUInt64 media w := ⟨(start.advance pre).toHeld,saved⟩
  obtain ⟨d,_⟩ := NativeFlushRestart.installedPublished valid saved.fresh.1 fits
  obtain ⟨t,pub,frame,stable⟩ := NativeManifestPublish.healthyPublish (io.pinned _ _ created r)
    (fun p t pc step arg => reports _ created p t pc (r.advance step) arg) FileFrame.refl (io.reserved start _ _ created) (start.advance pre).manifest d.unique
  simp only [proposal] at pub
  exact ⟨t,by simp [NativeFlush.store, flushTableWith, proposal, Bind.bind, instMonadEIO._aux_13, EST.bind, created, NativeFlush.publish,
    Native.checked, pub, Pure.pure, instMonadEIO._aux_5, EST.pure],r.advance frame,stable,w,created,frame.sameFile saved⟩

theorem healthy (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size)
    (candidate : Candidate (root / "tables") origin)
    (rows : ImmutableSSTable.Unified.modelBuild Alvoki.CRC32C.extend (tableLayout candidate.number.toUInt64)
      (s.mem.toList.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) {} = .ok (count, bytes))
    (writer : NativeTableWriter.Healthy (tablePath (root / "tables") candidate.number.toUInt64)
      candidate.number.toUInt64 s.mem.toList candidate.reserved)
    (dir : HealthyDirectory (tableNamespace physical root) s.mem.toList candidate)
    (reports : ∀ w, NativeFlush.createTable root s.mem.toList origin = .ok candidate.number.toUInt64 w →
      NativeManifestPublish.Healthy (root / "manifest") (L0Manifest.encode (proposal image s candidate.number.toUInt64)) w
        (Ready physical root lock ref wal image s candidate.number.toUInt64 media) manifest) :
    ∃ t, NativeFlush.store root image s origin = .ok ⟨proposal image s candidate.number.toUInt64, ∅⟩ t ∧
      Ready physical root lock ref wal image s candidate.number.toUInt64 media t ∧
      (physical t).manifest.Stable (L0Manifest.encode (proposal image s candidate.number.toUInt64)) := by
  obtain ⟨t,returned,ready,stable,_⟩ := healthyPinned io start valid fits candidate rows writer dir reports
  exact ⟨t,returned,ready,stable⟩

end ExperimentalL0.NativeFlushStore
