import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_107 :
    (List.ofFn coreChunks908_107).flatten =
      (coreData908.take (coreResources908 107).q).drop 185 := by
  decide +kernel

theorem coreCheck908_107 :
    ∀ c : Fin 1, (coreChunks908_107 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 107)) = true := by
  decide +kernel
#print axioms coreFlatten908_107
#print axioms coreCheck908_107
end Erdos883Verified
