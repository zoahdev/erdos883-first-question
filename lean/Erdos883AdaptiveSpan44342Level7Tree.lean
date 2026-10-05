import Erdos883AdaptiveSpan44342Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength44342_7 : adaptiveNumericSpans44342_7.length = 515 := by decide +kernel
theorem adaptiveSpanEvenCache44342_7 : adaptiveSpanEven44342_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain44342_7 : adaptiveSpanEven44342_7.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanEvenEntries44342_7 : adaptiveSpanEven44342_7.spans = coreEvenSpans 22171 0 adaptiveNumericSpans44342_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache44342_7 : adaptiveSpanWhole44342_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain44342_7 : adaptiveSpanWhole44342_7.domainCheck 22171 = true := by decide +kernel
theorem adaptiveSpanWholeEntries44342_7 : adaptiveSpanWhole44342_7.spans = coreWholeSpans 0 adaptiveNumericSpans44342_7 := by
  decide +kernel
end Erdos883Verified
