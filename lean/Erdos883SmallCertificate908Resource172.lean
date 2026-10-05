import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_172 :
    (List.ofFn coreChunks908_172).flatten =
      (coreData908.take (coreResources908 172).q).drop 290 := by
  decide +kernel

theorem coreCheck908_172 :
    ∀ c : Fin 1, (coreChunks908_172 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 172)) = true := by
  decide +kernel
#print axioms coreFlatten908_172
#print axioms coreCheck908_172
end Erdos883Verified
