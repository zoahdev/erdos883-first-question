import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_40 :
    (List.ofFn coreChunks680_40).flatten =
      (coreData680.take (coreResources680 40).q).drop 164 := by
  decide +kernel

theorem coreCheck680_40 :
    ∀ c : Fin 1, (coreChunks680_40 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 40)) = true := by
  decide +kernel
#print axioms coreFlatten680_40
#print axioms coreCheck680_40
end Erdos883Verified
