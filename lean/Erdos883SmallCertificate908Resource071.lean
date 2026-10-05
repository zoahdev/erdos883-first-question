import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_71 :
    (List.ofFn coreChunks908_71).flatten =
      (coreData908.take (coreResources908 71).q).drop 135 := by
  decide +kernel

theorem coreCheck908_71 :
    ∀ c : Fin 1, (coreChunks908_71 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 71)) = true := by
  decide +kernel
#print axioms coreFlatten908_71
#print axioms coreCheck908_71
end Erdos883Verified
