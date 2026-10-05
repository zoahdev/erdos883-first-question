import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_162 :
    (List.ofFn coreChunks908_162).flatten =
      (coreData908.take (coreResources908 162).q).drop 381 := by
  decide +kernel

theorem coreCheck908_162 :
    ∀ c : Fin 1, (coreChunks908_162 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 162)) = true := by
  decide +kernel
#print axioms coreFlatten908_162
#print axioms coreCheck908_162
end Erdos883Verified
