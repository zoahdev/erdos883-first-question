import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten825_111 :
    (List.ofFn coreChunks825_111).flatten =
      (coreData825.take (coreResources825 111).q).drop 203 := by
  decide +kernel

theorem coreCheck825_111 :
    ∀ c : Fin 1, (coreChunks825_111 c).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 111)) = true := by
  decide +kernel
#print axioms coreFlatten825_111
#print axioms coreCheck825_111
end Erdos883Verified
