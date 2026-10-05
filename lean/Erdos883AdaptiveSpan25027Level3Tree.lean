import Erdos883AdaptiveSpan25027Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_3 : adaptiveNumericSpans25027_3.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_3 : adaptiveSpanEven25027_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_3 : adaptiveSpanEven25027_3.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_3 : adaptiveSpanEven25027_3.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_3 : adaptiveSpanWhole25027_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_3 : adaptiveSpanWhole25027_3.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_3 : adaptiveSpanWhole25027_3.spans = coreWholeSpans 0 adaptiveNumericSpans25027_3 := by
  decide +kernel
end Erdos883Verified
