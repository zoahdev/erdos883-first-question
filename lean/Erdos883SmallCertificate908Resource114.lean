import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_114 :
    (List.ofFn coreChunks908_114).flatten =
      (coreData908.take (coreResources908 114).q).drop 197 := by
  decide +kernel

theorem coreCheck908_114 :
    ∀ c : Fin 1, (coreChunks908_114 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 114)) = true := by
  decide +kernel
#print axioms coreFlatten908_114
#print axioms coreCheck908_114
end Erdos883Verified
