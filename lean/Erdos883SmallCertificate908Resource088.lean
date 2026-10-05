import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_88 :
    (List.ofFn coreChunks908_88).flatten =
      (coreData908.take (coreResources908 88).q).drop 157 := by
  decide +kernel

theorem coreCheck908_88 :
    ∀ c : Fin 1, (coreChunks908_88 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 88)) = true := by
  decide +kernel
#print axioms coreFlatten908_88
#print axioms coreCheck908_88
end Erdos883Verified
