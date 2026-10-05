import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_146 :
    (List.ofFn coreChunks908_146).flatten =
      (coreData908.take (coreResources908 146).q).drop 281 := by
  decide +kernel

theorem coreCheck908_146 :
    ∀ c : Fin 1, (coreChunks908_146 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 146)) = true := by
  decide +kernel
#print axioms coreFlatten908_146
#print axioms coreCheck908_146
end Erdos883Verified
