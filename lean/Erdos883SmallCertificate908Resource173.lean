import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_173 :
    (List.ofFn coreChunks908_173).flatten =
      (coreData908.take (coreResources908 173).q).drop 293 := by
  decide +kernel

theorem coreCheck908_173 :
    ∀ c : Fin 1, (coreChunks908_173 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 173)) = true := by
  decide +kernel
#print axioms coreFlatten908_173
#print axioms coreCheck908_173
end Erdos883Verified
