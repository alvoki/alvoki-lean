# Publication proofs

[CheckpointPublicationModel.lean](CheckpointPublicationModel.lean) models run files and manifest choices across checkpoint publication cuts. The executable publication schedule is in [CheckpointPublication.lean](../../Publication/CheckpointPublication.lean).

The model states logical file and directory effects; the [native storage invariant map](../../../../../docs/proofs/native-storage.md) identifies the filesystem assumptions needed to connect those effects to native calls.

From `lean/`, run `lake build Alvoki.Storage.Proofs.Publication.CheckpointPublicationModel` and `lake env leanchecker Alvoki.Storage.Proofs.Publication.CheckpointPublicationModel` for this module. The [getting-started guide](../../../../../docs/getting-started.md) lists the full storage checks.
