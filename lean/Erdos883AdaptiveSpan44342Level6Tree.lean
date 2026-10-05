import Erdos883AdaptiveSpan44342Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_6 : adaptiveNumericSpans44342_6.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_6 : adaptiveSpanEven44342_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_6 : adaptiveSpanEven44342_6.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_6 : adaptiveSpanEven44342_6.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_6 : adaptiveSpanWhole44342_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_6 : adaptiveSpanWhole44342_6.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_6 : adaptiveSpanWhole44342_6.spans = coreWholeSpans 0 adaptiveNumericSpans44342_6 := by
  decide +kernel
end Erdos883Verified
