import Erdos883AdaptiveSpan25027Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength25027_6 : adaptiveNumericSpans25027_6.length = 450 := by decide +kernel
theorem adaptiveSpanEvenCache25027_6 : adaptiveSpanEven25027_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain25027_6 : adaptiveSpanEven25027_6.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanEvenEntries25027_6 : adaptiveSpanEven25027_6.spans = coreEvenSpans 12514 0 adaptiveNumericSpans25027_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache25027_6 : adaptiveSpanWhole25027_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain25027_6 : adaptiveSpanWhole25027_6.domainCheck 12514 = true := by decide +kernel
theorem adaptiveSpanWholeEntries25027_6 : adaptiveSpanWhole25027_6.spans = coreWholeSpans 0 adaptiveNumericSpans25027_6 := by
  decide +kernel
end Erdos883Verified
