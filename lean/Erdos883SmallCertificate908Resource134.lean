import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_134 :
    (List.ofFn coreChunks908_134).flatten =
      (coreData908.take (coreResources908 134).q).drop 234 := by
  decide +kernel

theorem coreCheck908_134 :
    ∀ c : Fin 1, (coreChunks908_134 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 134)) = true := by
  decide +kernel
#print axioms coreFlatten908_134
#print axioms coreCheck908_134
end Erdos883Verified
