import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck618 : coreOrderCheck 618 (coreData618.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten618 : (List.ofFn coreMetadataChunks618).flatten = coreData618 := by
  decide +kernel
#print axioms coreOrderCheck618
#print axioms coreMetadataFlatten618
end Erdos883Verified
