import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_104 :
    (List.ofFn coreChunks908_104).flatten =
      (coreData908.take (coreResources908 104).q).drop 182 := by
  decide +kernel

theorem coreCheck908_104 :
    ∀ c : Fin 1, (coreChunks908_104 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 104)) = true := by
  decide +kernel
#print axioms coreFlatten908_104
#print axioms coreCheck908_104
end Erdos883Verified
