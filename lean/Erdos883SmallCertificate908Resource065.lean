import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_65 :
    (List.ofFn coreChunks908_65).flatten =
      (coreData908.take (coreResources908 65).q).drop 111 := by
  decide +kernel

theorem coreCheck908_65 :
    ∀ c : Fin 1, (coreChunks908_65 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 65)) = true := by
  decide +kernel
#print axioms coreFlatten908_65
#print axioms coreCheck908_65
end Erdos883Verified
