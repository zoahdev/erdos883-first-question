import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_163 :
    (List.ofFn coreChunks908_163).flatten =
      (coreData908.take (coreResources908 163).q).drop 382 := by
  decide +kernel

theorem coreCheck908_163 :
    ∀ c : Fin 1, (coreChunks908_163 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 163)) = true := by
  decide +kernel
#print axioms coreFlatten908_163
#print axioms coreCheck908_163
end Erdos883Verified
