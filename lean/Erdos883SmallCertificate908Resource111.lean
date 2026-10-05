import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_111 :
    (List.ofFn coreChunks908_111).flatten =
      (coreData908.take (coreResources908 111).q).drop 193 := by
  decide +kernel

theorem coreCheck908_111 :
    ∀ c : Fin 1, (coreChunks908_111 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 111)) = true := by
  decide +kernel
#print axioms coreFlatten908_111
#print axioms coreCheck908_111
end Erdos883Verified
