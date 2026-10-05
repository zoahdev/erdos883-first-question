import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_60 :
    (List.ofFn coreChunks908_60).flatten =
      (coreData908.take (coreResources908 60).q).drop 223 := by
  decide +kernel

theorem coreCheck908_60 :
    ∀ c : Fin 1, (coreChunks908_60 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 60)) = true := by
  decide +kernel
#print axioms coreFlatten908_60
#print axioms coreCheck908_60
end Erdos883Verified
