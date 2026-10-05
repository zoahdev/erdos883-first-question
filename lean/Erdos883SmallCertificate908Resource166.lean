import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_166 :
    (List.ofFn coreChunks908_166).flatten =
      (coreData908.take (coreResources908 166).q).drop 390 := by
  decide +kernel

theorem coreCheck908_166 :
    ∀ c : Fin 1, (coreChunks908_166 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 166)) = true := by
  decide +kernel
#print axioms coreFlatten908_166
#print axioms coreCheck908_166
end Erdos883Verified
