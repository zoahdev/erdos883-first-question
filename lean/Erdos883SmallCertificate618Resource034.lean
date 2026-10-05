import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_34 :
    (List.ofFn coreChunks618_34).flatten =
      (coreData618.take (coreResources618 34).q).drop 151 := by
  decide +kernel

theorem coreCheck618_34 :
    ∀ c : Fin 1, (coreChunks618_34 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 34)) = true := by
  decide +kernel
#print axioms coreFlatten618_34
#print axioms coreCheck618_34
end Erdos883Verified
