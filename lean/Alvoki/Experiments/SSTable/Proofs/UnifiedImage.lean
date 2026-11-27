import Alvoki.Experiments.SSTable.Proofs.UnifiedMetadata
import Alvoki.Experiments.SSTable.UnifiedReader

namespace ImmutableSSTable.Unified

structure DataGroup where
  ref : Ref
  rows : Array Entry

structure LeafGroup where
  ref : Ref
  blocks : Array DataGroup

def LeafGroup.rows (group : LeafGroup) : List Entry :=
  group.blocks.toList.flatMap (·.rows.toList)

structure PacketAt (crc : Checksum) (id kind : UInt64) (image : ByteArray)
    (offset size : Nat) (body : ByteArray) : Prop where
  size_eq : size = body.size + checksumSize
  bounded : size ≤ maxRowSize
  extent : offset + size ≤ image.size
  slice : image.extract offset (offset + size) = encodePacket crc id kind offset body

structure DataGroup.InImage (layout : Layout) (crc : Checksum) (image : ByteArray)
    (group : DataGroup) : Prop where
  count_eq : group.ref.count = group.rows.size
  nonempty : 0 < group.rows.size
  lastKey : (group.rows.back?).map Entry.key = some group.ref.lastKey
  rowFits : ∀ row ∈ group.rows.toList, rowFits layout row = true
  packet : PacketAt crc layout.tableId 1 image group.ref.offset group.ref.size
    (encodeData layout group.rows)

structure LeafGroup.InImage (layout : Layout) (crc : Checksum) (image : ByteArray)
    (leaf : LeafGroup) : Prop where
  refs : ValidRefs (leaf.blocks.map DataGroup.ref)
  bounds : checkChildren (leaf.blocks.map DataGroup.ref) leaf.ref.firstRow leaf.ref.count
    leaf.ref.offset = .ok ()
  lastKey : ((leaf.blocks.map DataGroup.ref).back?).map Ref.lastKey = some leaf.ref.lastKey
  packet : PacketAt crc layout.tableId 2 image leaf.ref.offset leaf.ref.size
    (encodeIndex (leaf.blocks.map DataGroup.ref))
  blocks : ∀ group ∈ leaf.blocks.toList, group.InImage layout crc image

/-- The actual bytes produced by the successful streaming schedule. The
witness records row partitions and the byte ranges that the reader uses. -/
structure Image (crc : Checksum) (layout : Layout) (rows : List Entry) (image : ByteArray) : Prop where
  ordered : Ordered rows
  extent : image.size ≤ maxFileSize
  exists_layout : ∃ (footer : Footer) (groups : Array LeafGroup),
    footer.layout = layout ∧ footer.count = rows.length ∧
    groups.toList.flatMap LeafGroup.rows = rows ∧ footer.Valid ∧
    image.extract (image.size - (footerBodySize + checksumSize)) image.size =
      encodePacket crc 0 4 0 (encodeFooterBody footer) ∧
    footerBodySize + checksumSize ≤ image.size ∧
    (∀ leaf ∈ groups.toList, leaf.InImage layout crc image) ∧
    (if rows.isEmpty then groups.isEmpty = true ∧ image.size = footerBodySize + checksumSize
     else ValidRefs (groups.map LeafGroup.ref) ∧
       checkChildren (groups.map LeafGroup.ref) 0 rows.length footer.rootOffset = .ok () ∧
       footer.rootOffset + footer.rootSize = image.size - (footerBodySize + checksumSize) ∧
       PacketAt crc layout.tableId 3 image footer.rootOffset footer.rootSize
         (encodeIndex (groups.map LeafGroup.ref)))

end ImmutableSSTable.Unified
