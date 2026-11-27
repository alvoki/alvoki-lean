# Durable publication

A reader after restart must be able to identify a complete set of files. These modules describe the order in which the engine writes data, changes names and makes those names durable.

- **Replace one name.** Write a staging file, sync it, rename it onto the target and sync the containing directory. The WAL commit marker uses this pattern. [Replacement schedule](DiskPublication.lean)
- **Publish a checkpoint.** Write and sync the generation’s runs, sync their directory entries, then publish the manifest that names them. [Checkpoint schedule](CheckpointPublication.lean)
- **Finish collection.** Given an approved list, unlink its names and sync the directory. The caller supplies the eligibility decision. [Collection schedule](RunCollection.lean)

For crash behavior, the [file replacement model](DiskPublicationModel.lean) describes visible and durable outcomes. The [directory model](DirectoryPublicationModel.lean) tracks which [manifest and marker bindings](DirectoryBindings.lean) can survive together. The disk adapter supplies the native operations. [Filesystem contract](../../../../docs/proofs/filesystem.md)
