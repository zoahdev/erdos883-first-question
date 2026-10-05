import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_77 :
    (List.ofFn coreChunks908_77).flatten =
      (coreData908.take (coreResources908 77).q).drop 142 := by
  decide +kernel

theorem coreCheck908_77 :
    ∀ c : Fin 1, (coreChunks908_77 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 77)) = true := by
  decide +kernel
#print axioms coreFlatten908_77
#print axioms coreCheck908_77
end Erdos883Verified
