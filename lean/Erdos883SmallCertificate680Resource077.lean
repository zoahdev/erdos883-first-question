import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_77 :
    (List.ofFn coreChunks680_77).flatten =
      (coreData680.take (coreResources680 77).q).drop 144 := by
  decide +kernel

theorem coreCheck680_77 :
    ∀ c : Fin 1, (coreChunks680_77 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 77)) = true := by
  decide +kernel
#print axioms coreFlatten680_77
#print axioms coreCheck680_77
end Erdos883Verified
