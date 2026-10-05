import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_145 :
    (List.ofFn coreChunks908_145).flatten =
      (coreData908.take (coreResources908 145).q).drop 277 := by
  decide +kernel

theorem coreCheck908_145 :
    ∀ c : Fin 1, (coreChunks908_145 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 145)) = true := by
  decide +kernel
#print axioms coreFlatten908_145
#print axioms coreCheck908_145
end Erdos883Verified
