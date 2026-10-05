import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_27 :
    (List.ofFn coreChunks680_27).flatten =
      (coreData680.take (coreResources680 27).q).drop 145 := by
  decide +kernel

theorem coreCheck680_27 :
    ∀ c : Fin 1, (coreChunks680_27 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 27)) = true := by
  decide +kernel
#print axioms coreFlatten680_27
#print axioms coreCheck680_27
end Erdos883Verified
