import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_152 :
    (List.ofFn coreChunks908_152).flatten =
      (coreData908.take (coreResources908 152).q).drop 304 := by
  decide +kernel

theorem coreCheck908_152 :
    ∀ c : Fin 1, (coreChunks908_152 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 152)) = true := by
  decide +kernel
#print axioms coreFlatten908_152
#print axioms coreCheck908_152
end Erdos883Verified
